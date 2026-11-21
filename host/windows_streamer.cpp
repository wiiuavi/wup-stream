/* Windows desktop/audio streamer for libwupstream. */
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <winsock2.h>
#include <ws2tcpip.h>
#include <commctrl.h>
#include <shellapi.h>
#include <mmdeviceapi.h>
#include <audioclient.h>
#include <functiondiscoverykeys_devpkey.h>
#include <stdint.h>
#include <math.h>
#include <atomic>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <vector>
#include "wupstream.h"

static void key(WORD vk, bool down) {
    INPUT i = {}; i.type = INPUT_KEYBOARD; i.ki.wVk = vk;
    if (!down) i.ki.dwFlags = KEYEVENTF_KEYUP;
    SendInput(1, &i, sizeof i);
}
/* Indexed by the libwupstream button bit, then four left-stick and four right-stick directions. */
static const WORD control_keys[24] = {0,'P',VK_BACK,VK_RETURN,'C','Z','E','Q',VK_DOWN,VK_UP,VK_RIGHT,VK_LEFT,'I','U','K','J','W','S','A','D','T','G','F','H'};
static std::atomic<HWND> main_window(NULL);
static HWND capture_button = NULL, input_button = NULL;
static HWND mouse_button = NULL, click_button = NULL;
static HWND display_button = NULL, keep_display_button = NULL, display_status_label = NULL, bitrate_button = NULL;
static HWND latency_button = NULL;
static HWND sensitivity_slider = NULL, sensitivity_label = NULL;
static HWND connect_button = NULL, connection_label = NULL;
static HWND hotspot_button = NULL, hotspot_info_label = NULL;
static std::atomic<bool> capture_on(true), input_on(true), window_closed(false);
static char pc_addresses[512] = "PC IPv4: ";
static std::atomic<int> mouse_mode(0), click_mode(0), mouse_sensitivity(8), bitrate_mode(0);
static std::atomic<bool> high_latency(false);
static char settings_path[MAX_PATH] = {};
static bool sent_left = false, sent_right = false;
static double mouse_remainder_x = 0, mouse_remainder_y = 0;
static double dpad_ramp = 0;
static const char *connect_ip = NULL;
static HANDLE connect_thread = NULL;
static volatile LONG connect_done = 0;
static std::atomic<bool> connecting(false);
static std::atomic<bool> ui_connected(false), disconnect_requested(false);
static wupstream *connect_result = NULL;
static int connect_bitrate_kbps = 10000;
static std::atomic<bool> reconnect_requested(false);
static std::atomic<int> pending_display_action(0); /* 1 apply, 2 confirm, 3 restore, 4 toggle */
static HANDLE gui_ready_event = NULL, gui_thread_handle = NULL;
static const UINT WM_APP_SET_TEXT = WM_APP+1, WM_APP_DISPLAY_STATE = WM_APP+2, WM_APP_CONNECTION_STATE = WM_APP+3, WM_APP_REFRESH_BUTTONS = WM_APP+4;
static bool display_backup_ready = false, display_active = false, display_pending = false;
static ULONGLONG display_confirm_deadline = 0;
static char display_backup_path[MAX_PATH] = {};
static char display_status[256] = "Preparing primary-display backup...";

struct DisplayBackupRecord {
    char magic[8]; DWORD version, active; char device[CCHDEVICENAME]; DEVMODEA mode;
};
static void update_buttons();

static void send_mouse_button(DWORD down_flag, DWORD up_flag, bool down) {
    INPUT i = {}; i.type = INPUT_MOUSE; i.mi.dwFlags = down ? down_flag : up_flag; SendInput(1, &i, sizeof i);
}
static void sync_mouse_buttons(bool touched, uint32_t buttons, bool enabled) {
    bool left = enabled && touched, right = false;
    if (enabled && click_mode == 1) { left |= (buttons & WUPSTREAM_A) != 0; right = (buttons & WUPSTREAM_B) != 0; }
    if (enabled && click_mode == 2) { left = touched || (buttons & WUPSTREAM_ZL); right = (buttons & WUPSTREAM_ZR) != 0; }
    if (enabled && click_mode == 3) { left = touched || (buttons & WUPSTREAM_ZR); right = (buttons & WUPSTREAM_ZL) != 0; }
    if (left != sent_left) send_mouse_button(MOUSEEVENTF_LEFTDOWN, MOUSEEVENTF_LEFTUP, left);
    if (right != sent_right) send_mouse_button(MOUSEEVENTF_RIGHTDOWN, MOUSEEVENTF_RIGHTUP, right);
    sent_left = left; sent_right = right;
}
static void move_mouse_from_stick(const wupstream_input_t &in, double dt) {
    if (!mouse_mode || dt <= 0) return;
    int xaxis, yaxis;
    if (mouse_mode == 3) {
        xaxis = ((in.buttons & WUPSTREAM_RIGHT) ? 1100 : 0) - ((in.buttons & WUPSTREAM_LEFT) ? 1100 : 0);
        yaxis = ((in.buttons & WUPSTREAM_UP) ? 1100 : 0) - ((in.buttons & WUPSTREAM_DOWN) ? 1100 : 0);
        if (xaxis && yaxis) { xaxis = (int)(xaxis * 0.7071); yaxis = (int)(yaxis * 0.7071); }
        dpad_ramp += (xaxis || yaxis ? 1.0 : -1.0) * dt / 0.12;
        if (dpad_ramp < 0) dpad_ramp = 0;
        if (dpad_ramp > 1) dpad_ramp = 1;
        xaxis = (int)(xaxis * dpad_ramp); yaxis = (int)(yaxis * dpad_ramp);
    } else {
        dpad_ramp = 0;
        xaxis = mouse_mode == 1 ? in.lx : in.rx;
        yaxis = mouse_mode == 1 ? in.ly : in.ry;
        if (abs(xaxis) < 90) xaxis = 0;
        if (abs(yaxis) < 90) yaxis = 0;
    }
    if (!xaxis && !yaxis) return;
    const double speed = mouse_sensitivity * (mouse_mode == 3 ? 75.0 : 120.0);
    double dx = xaxis / 1100.0 * speed * dt + mouse_remainder_x;
    double dy = -yaxis / 1100.0 * speed * dt + mouse_remainder_y;
    int stepx = (int)dx, stepy = (int)dy;
    mouse_remainder_x = dx - stepx; mouse_remainder_y = dy - stepy;
    if (!stepx && !stepy) return;
    INPUT m = {}; m.type = INPUT_MOUSE; m.mi.dx = stepx; m.mi.dy = stepy; m.mi.dwFlags = MOUSEEVENTF_MOVE;
    SendInput(1, &m, sizeof m);
}
static void move_mouse_from_touch(const wupstream_input_t &in) {
    int width = GetSystemMetrics(SM_CXSCREEN), height = GetSystemMetrics(SM_CYSCREEN);
    int x = in.tx * (width-1) / (WUPSTREAM_W-1), y = in.ty * (height-1) / (WUPSTREAM_H-1);
    POINT current;
    if (GetCursorPos(&current) && (current.x != x || current.y != y)) {
        INPUT m = {}; m.type = INPUT_MOUSE; m.mi.dx = x * 65535 / (width-1); m.mi.dy = y * 65535 / (height-1);
        m.mi.dwFlags = MOUSEEVENTF_MOVE | MOUSEEVENTF_ABSOLUTE; SendInput(1, &m, sizeof m);
    }
}

static const char *mouse_mode_name() { return mouse_mode == 1 ? "left joystick" : mouse_mode == 2 ? "right joystick" : mouse_mode == 3 ? "D-pad" : "none"; }
static const char *click_mode_name() { return click_mode == 1 ? "A/B" : click_mode == 2 ? "triggers" : click_mode == 3 ? "triggers inverted" : "none"; }
static const char *bitrate_name() { return bitrate_mode == 1 ? "5 Mbps" : bitrate_mode == 2 ? "2.5 Mbps" : "10 Mbps"; }
static void save_settings() {
    if (!settings_path[0]) return;
    char value[16]; _snprintf(value, sizeof value, "%d", mouse_mode.load()); WritePrivateProfileStringA("Input", "MouseControl", value, settings_path);
    _snprintf(value, sizeof value, "%d", click_mode.load()); WritePrivateProfileStringA("Input", "ClickMapping", value, settings_path);
    _snprintf(value, sizeof value, "%d", mouse_sensitivity.load()); WritePrivateProfileStringA("Input", "MouseSensitivity", value, settings_path);
    _snprintf(value, sizeof value, "%d", bitrate_mode.load()); WritePrivateProfileStringA("Video", "BitrateMode", value, settings_path);
    _snprintf(value, sizeof value, "%d", high_latency ? 1 : 0); WritePrivateProfileStringA("Video", "HighLatency", value, settings_path);
}
static void load_settings() {
    char root[MAX_PATH] = {}; DWORD n = GetEnvironmentVariableA("LOCALAPPDATA", root, MAX_PATH);
    if (n && n < MAX_PATH-16) {
        _snprintf(settings_path, sizeof(settings_path), "%s\\WupStream", root);
        CreateDirectoryA(settings_path, NULL);
        strncat(settings_path, "\\settings.ini", sizeof(settings_path)-strlen(settings_path)-1);
    } else {
        char path[MAX_PATH] = {}; n = GetModuleFileNameA(NULL, path, MAX_PATH);
        if (!n || n >= MAX_PATH) return;
        char *slash = strrchr(path, '\\'); if (!slash) slash = strrchr(path, '/');
        if (!slash) return;
        *(slash + 1) = 0;
        size_t path_len = strlen(path);
        if (path_len >= sizeof(settings_path)-1) return;
        memcpy(settings_path, path, path_len+1);
        strncat(settings_path, "wup-stream.ini", sizeof(settings_path)-strlen(settings_path)-1);
    }
    mouse_mode = GetPrivateProfileIntA("Input", "MouseControl", 0, settings_path);
    click_mode = GetPrivateProfileIntA("Input", "ClickMapping", 0, settings_path);
    mouse_sensitivity = GetPrivateProfileIntA("Input", "MouseSensitivity", 8, settings_path);
    bitrate_mode = GetPrivateProfileIntA("Video", "BitrateMode", 0, settings_path);
    high_latency = GetPrivateProfileIntA("Video", "HighLatency", 0, settings_path) != 0;
    if (mouse_mode < 0 || mouse_mode > 3) mouse_mode = 0;
    if (click_mode < 0 || click_mode > 3) click_mode = 0;
    if (mouse_sensitivity < 1 || mouse_sensitivity > 10) mouse_sensitivity = 8;
    if (bitrate_mode < 0 || bitrate_mode > 2) bitrate_mode = 0;
}

static bool primary_device(char name[CCHDEVICENAME], DEVMODEA *current) {
    name[0] = 0;
    for (DWORD i = 0;; ++i) {
        DISPLAY_DEVICEA dd = {}; dd.cb = sizeof dd;
        if (!EnumDisplayDevicesA(NULL, i, &dd, 0)) break;
        if (dd.StateFlags & DISPLAY_DEVICE_PRIMARY_DEVICE) { memcpy(name, dd.DeviceName, CCHDEVICENAME); name[CCHDEVICENAME-1] = 0; break; }
    }
    current->dmSize = sizeof *current; current->dmDriverExtra = 0;
    return EnumDisplaySettingsA(name[0] ? name : NULL, ENUM_CURRENT_SETTINGS, current) != 0;
}
static DEVMODEA public_mode(const DEVMODEA &src) {
    DEVMODEA m = {}; m.dmSize = sizeof m; m.dmDriverExtra = 0;
    m.dmFields = DM_BITSPERPEL | DM_PELSWIDTH | DM_PELSHEIGHT;
    m.dmBitsPerPel = src.dmBitsPerPel; m.dmPelsWidth = src.dmPelsWidth; m.dmPelsHeight = src.dmPelsHeight;
    if (src.dmFields & DM_DISPLAYFREQUENCY) { m.dmFields |= DM_DISPLAYFREQUENCY; m.dmDisplayFrequency = src.dmDisplayFrequency; }
    return m;
}
static bool read_display_backup(DisplayBackupRecord *r) {
    HANDLE f = CreateFileA(display_backup_path, GENERIC_READ, FILE_SHARE_READ, NULL, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL);
    if (f == INVALID_HANDLE_VALUE) return false;
    DWORD n = 0; bool ok = ReadFile(f, r, sizeof *r, &n, NULL) && n == sizeof *r; CloseHandle(f);
    return ok && !memcmp(r->magic, "WUPDSP1", 7) && r->version == 1 && r->mode.dmSize == sizeof(DEVMODEA);
}
static bool write_display_backup(const DisplayBackupRecord &r) {
    char temp[MAX_PATH]; size_t n = strlen(display_backup_path);
    if (!n || n + 5 >= sizeof temp) return false;
    memcpy(temp, display_backup_path, n); memcpy(temp+n, ".tmp", 5);
    HANDLE f = CreateFileA(temp, GENERIC_WRITE, 0, NULL, CREATE_ALWAYS, FILE_ATTRIBUTE_NORMAL, NULL);
    if (f == INVALID_HANDLE_VALUE) return false;
    DWORD wrote = 0; bool ok = WriteFile(f, &r, sizeof r, &wrote, NULL) && wrote == sizeof r && FlushFileBuffers(f);
    CloseHandle(f);
    if (ok) ok = MoveFileExA(temp, display_backup_path, MOVEFILE_REPLACE_EXISTING | MOVEFILE_WRITE_THROUGH) != 0;
    if (!ok) DeleteFileA(temp);
    return ok;
}
static bool set_display_mode(const DisplayBackupRecord &r) {
    DEVMODEA mode = r.mode; mode.dmSize = sizeof mode; mode.dmDriverExtra = 0;
    LPCSTR device = r.device[0] ? r.device : NULL;
    if (ChangeDisplaySettingsExA(device, &mode, NULL, CDS_TEST, NULL) != DISP_CHANGE_SUCCESSFUL) return false;
    return ChangeDisplaySettingsExA(device, &mode, NULL, CDS_FULLSCREEN, NULL) == DISP_CHANGE_SUCCESSFUL;
}
static bool initialize_display_backup() {
    char exe[MAX_PATH] = {}; DWORD n = GetModuleFileNameA(NULL, exe, MAX_PATH);
    if (!n || n >= MAX_PATH) { strcpy(display_status, "Display backup unavailable: cannot locate the executable."); return false; }
    char *slash = strrchr(exe, '\\'); if (!slash) slash = strrchr(exe, '/');
    if (!slash) { strcpy(display_status, "Display backup unavailable: cannot locate the executable folder."); return false; }
    *(slash+1) = 0;
    if (strlen(exe) + strlen("wup-stream-display-backup.bin") >= sizeof display_backup_path) { strcpy(display_status, "Display backup path is too long."); return false; }
    strcpy(display_backup_path, exe); strcat(display_backup_path, "wup-stream-display-backup.bin");
    DWORD attr = GetFileAttributesA(display_backup_path);
    if (attr != INVALID_FILE_ATTRIBUTES) {
        DisplayBackupRecord old = {};
        if (!read_display_backup(&old)) { strcpy(display_status, "Display backup is unreadable; mode changes disabled."); return false; }
        if (old.active) {
            if (!set_display_mode(old)) { strcpy(display_status, "Could not recover the prior display mode; backup preserved."); return false; }
            old.active = 0;
            if (!write_display_backup(old)) { strcpy(display_status, "Recovered display, but could not update backup file."); return false; }
        }
    }
    DEVMODEA current = {}; char device[CCHDEVICENAME] = {};
    if (!primary_device(device, &current)) { strcpy(display_status, "Could not read primary display mode."); return false; }
    DisplayBackupRecord r = {}; memcpy(r.magic, "WUPDSP1", 7); r.version = 1; memcpy(r.device, device, sizeof r.device); r.device[sizeof r.device-1] = 0; r.mode = public_mode(current);
    if (!write_display_backup(r)) { strcpy(display_status, "Cannot write display backup beside the EXE; mode changes disabled."); return false; }
    display_backup_ready = true; strcpy(display_status, "Original primary display mode backed up beside the EXE."); return true;
}
static bool choose_gamepad_mode(const char *device, const DEVMODEA &current, DEVMODEA *chosen) {
    bool found = false; double best = 1e100; const double aspect = 854.0/480.0; const long long area = 854LL*480LL;
    for (DWORD i = 0;; ++i) {
        DEVMODEA candidate = {}; candidate.dmSize = sizeof candidate; candidate.dmDriverExtra = 0;
        if (!EnumDisplaySettingsA(device[0] ? device : NULL, i, &candidate)) break;
        if (!candidate.dmPelsWidth || !candidate.dmPelsHeight || candidate.dmBitsPerPel != current.dmBitsPerPel) continue;
        double a = (double)candidate.dmPelsWidth / candidate.dmPelsHeight;
        long long pixels = (long long)candidate.dmPelsWidth * candidate.dmPelsHeight;
        double score = fabs(a-aspect)*1000000000.0 + (double)llabs(pixels-area);
        int hz = candidate.dmDisplayFrequency > 1 ? candidate.dmDisplayFrequency : 60;
        score += abs(hz-60)*100.0;
        if (score < best) { best = score; *chosen = public_mode(candidate); found = true; }
    }
    return found;
}
static bool apply_gamepad_display() {
    DEVMODEA current = {}; char device[CCHDEVICENAME] = {};
    if (!primary_device(device, &current)) { strcpy(display_status, "Could not read current display mode."); return false; }
    DisplayBackupRecord r = {}; memcpy(r.magic, "WUPDSP1", 7); r.version = 1; r.active = 1;
    memcpy(r.device, device, sizeof r.device); r.device[sizeof r.device-1] = 0; r.mode = public_mode(current);
    if (!write_display_backup(r)) { strcpy(display_status, "Backup write failed; display was not changed."); return false; }
    DEVMODEA target = {};
    if (!choose_gamepad_mode(device, current, &target)) { r.active = 0; write_display_backup(r); strcpy(display_status, "No compatible 32-bit display mode was found."); return false; }
    DEVMODEA original = r.mode; r.mode = target;
    if (!set_display_mode(r)) { r.mode = original; r.active = 0; write_display_backup(r); strcpy(display_status, "Windows rejected the GamePad display mode; original mode is unchanged."); return false; }
    r.mode = original;
    /* The backup file always stores the original mode, including while the alternate mode is active. */
    if (!write_display_backup(r)) {
        set_display_mode(r); r.active = 0; write_display_backup(r);
        strcpy(display_status, "Could not persist the restore record; reverted the display."); return false;
    }
    display_active = true; display_pending = true; display_confirm_deadline = GetTickCount64()+15000;
    _snprintf(display_status, sizeof display_status, "Using %lux%lu. Click Keep within 15 seconds; otherwise it restores.", (unsigned long)target.dmPelsWidth, (unsigned long)target.dmPelsHeight);
    return true;
}
static bool restore_display() {
    DisplayBackupRecord r = {};
    if (!read_display_backup(&r)) { strcpy(display_status, "Cannot read the display restore backup."); return false; }
    if (r.active && !set_display_mode(r)) { strcpy(display_status, "Windows could not restore the backed-up display mode; backup retained."); return false; }
    r.active = 0;
    if (!write_display_backup(r)) { strcpy(display_status, "Display restored, but backup status could not be updated."); }
    else strcpy(display_status, "Original primary display mode restored.");
    display_active = false; display_pending = false; return true;
}
static void process_display_request() {
    int action = pending_display_action.exchange(0);
    bool changed = action != 0;
    if (action == 4) action = display_active ? 3 : 1;
    if (action == 1 && !display_active) apply_gamepad_display();
    else if (action == 2 && display_active && display_pending) { display_pending = false; strcpy(display_status, "GamePad-compatible display mode kept until restore or exit."); }
    else if (action == 3 && display_active) restore_display();
    if (display_pending && GetTickCount64() >= display_confirm_deadline) { restore_display(); changed = true; }
    if (changed && main_window) {
        char *status = new char[strlen(display_status)+1]; strcpy(status, display_status);
        LPARAM bits = (display_backup_ready ? 1 : 0) | (display_active ? 2 : 0) | (display_pending ? 4 : 0);
        if (!PostMessageA(main_window, WM_APP_DISPLAY_STATE, (WPARAM)bits, (LPARAM)status)) delete[] status;
    }
}

static void set_text_if_changed(HWND hwnd, const char *text) {
    if (!hwnd) return;
    char old[512] = {};
    GetWindowTextA(hwnd, old, sizeof old);
    if (strcmp(old, text)) SetWindowTextA(hwnd, text);
}
static void post_connection_update(bool connected, const char *status) {
    if (!main_window) return;
    char *copy = new char[strlen(status)+1]; strcpy(copy, status);
    if (!PostMessageA(main_window, WM_APP_CONNECTION_STATE, connected ? 1 : 0, (LPARAM)copy)) delete[] copy;
}
static void update_display_controls(unsigned state, const char *status) {
    bool backup = (state & 1) != 0, active = (state & 2) != 0, pending = (state & 4) != 0;
    const char *label = !backup ? "GamePad display mode unavailable (backup failed)" :
        active ? "Restore original primary display mode" : "Switch primary display to GamePad mode";
    set_text_if_changed(display_button, label);
    if (display_button && !!IsWindowEnabled(display_button) != backup) EnableWindow(display_button, backup);
    if (keep_display_button && !!IsWindowVisible(keep_display_button) != pending) ShowWindow(keep_display_button, pending ? SW_SHOW : SW_HIDE);
    set_text_if_changed(display_status_label, status);
}

static void update_buttons() {
    if (capture_button) set_text_if_changed(capture_button, capture_on ? "Desktop + audio: ON  (F8)" : "Desktop + audio: OFF  (F8)");
    if (input_button) set_text_if_changed(input_button, input_on ? "GamePad input: ON  (F9)" : "GamePad input: OFF  (F9)");
    if (mouse_button) { char text[128]; _snprintf(text, sizeof text, "Mouse control: %s  (click to cycle)", mouse_mode_name()); set_text_if_changed(mouse_button, text); }
    if (click_button) { char text[128]; _snprintf(text, sizeof text, "Mouse clicks: %s  (click to cycle)", click_mode_name()); set_text_if_changed(click_button, text); }
    if (bitrate_button) { char text[128]; _snprintf(text, sizeof text, "Video bitrate: %s  (change reconnects)", bitrate_name()); set_text_if_changed(bitrate_button, text); }
    if (latency_button) set_text_if_changed(latency_button, high_latency ? "High-latency buffer: ON  (change reconnects)" : "High-latency buffer: OFF  (change reconnects)");
    if (sensitivity_label) { char text[64]; _snprintf(text, sizeof text, "Joystick mouse sensitivity: %d / 10", mouse_sensitivity.load()); set_text_if_changed(sensitivity_label, text); }
}

static DWORD WINAPI connect_worker(void *) {
    char value[16]; _snprintf(value, sizeof value, "%d", connect_bitrate_kbps); _putenv_s("WUPSTREAM_KBPS", value);
    _putenv_s("WUPSTREAM_HIGH_LATENCY", high_latency ? "1" : "0");
    _putenv_s("WUPSTREAM_PACKET_DELAY_US", high_latency ? "350" : "200");
    connect_result = wupstream_open(connect_ip, 3000);
    InterlockedExchange(&connect_done, 1);
    return 0;
}
static void start_connect() {
    if (connecting || connect_thread || window_closed) return;
    connect_bitrate_kbps = bitrate_mode == 1 ? 5000 : bitrate_mode == 2 ? 2500 : 10000;
    connecting = true; connect_done = 0; connect_result = NULL;
    if (connection_label) SetWindowTextA(connection_label, "Searching for GamePad (3 seconds)...");
    if (connect_button) EnableWindow(connect_button, FALSE);
    connect_thread = CreateThread(NULL, 0, connect_worker, NULL, 0, NULL);
    if (!connect_thread) {
        connecting = false;
        if (connection_label) SetWindowTextA(connection_label, "Could not start connection search.");
        if (connect_button) EnableWindow(connect_button, TRUE);
    }
}

static void open_hotspot_settings() {
    ShellExecuteA(NULL, "open", "ms-settings:network-mobilehotspot", NULL, NULL, SW_SHOWNORMAL);
}

static LRESULT CALLBACK window_proc(HWND hwnd, UINT msg, WPARAM wp, LPARAM lp) {
    switch (msg) {
    case WM_CREATE:
        CreateWindowA("STATIC", pc_addresses, WS_CHILD|WS_VISIBLE, 18, 12, 470, 24, hwnd, NULL, NULL, NULL);
        connection_label = CreateWindowA("STATIC", "Not connected", WS_CHILD|WS_VISIBLE, 18, 38, 430, 24, hwnd, NULL, NULL, NULL);
        capture_button = CreateWindowA("BUTTON", "", WS_CHILD|WS_VISIBLE|WS_TABSTOP|BS_PUSHBUTTON, 18, 68, 470, 34, hwnd, (HMENU)1001, NULL, NULL);
        input_button = CreateWindowA("BUTTON", "", WS_CHILD|WS_VISIBLE|WS_TABSTOP|BS_PUSHBUTTON, 18, 106, 470, 34, hwnd, (HMENU)1002, NULL, NULL);
        mouse_button = CreateWindowA("BUTTON", "", WS_CHILD|WS_VISIBLE|WS_TABSTOP|BS_PUSHBUTTON, 18, 144, 470, 34, hwnd, (HMENU)1003, NULL, NULL);
        click_button = CreateWindowA("BUTTON", "", WS_CHILD|WS_VISIBLE|WS_TABSTOP|BS_PUSHBUTTON, 18, 182, 470, 34, hwnd, (HMENU)1004, NULL, NULL);
        bitrate_button = CreateWindowA("BUTTON", "", WS_CHILD|WS_VISIBLE|WS_TABSTOP|BS_PUSHBUTTON, 18, 220, 470, 34, hwnd, (HMENU)1006, NULL, NULL);
        latency_button = CreateWindowA("BUTTON", "", WS_CHILD|WS_VISIBLE|WS_TABSTOP|BS_PUSHBUTTON, 18, 258, 470, 34, hwnd, (HMENU)1010, NULL, NULL);
        display_button = CreateWindowA("BUTTON", "", WS_CHILD|WS_VISIBLE|WS_TABSTOP|BS_PUSHBUTTON, 18, 296, 470, 34, hwnd, (HMENU)1008, NULL, NULL);
        keep_display_button = CreateWindowA("BUTTON", "Keep display mode", WS_CHILD|WS_VISIBLE|WS_TABSTOP|BS_PUSHBUTTON, 18, 334, 470, 32, hwnd, (HMENU)1009, NULL, NULL);
        sensitivity_label = CreateWindowA("STATIC", "", WS_CHILD|WS_VISIBLE, 18, 372, 470, 22, hwnd, NULL, NULL, NULL);
        sensitivity_slider = CreateWindowA(TRACKBAR_CLASSA, "", WS_CHILD|WS_VISIBLE|WS_TABSTOP|TBS_AUTOTICKS, 18, 394, 470, 32, hwnd, (HMENU)1007, NULL, NULL);
        SendMessageA(sensitivity_slider, TBM_SETRANGE, TRUE, MAKELONG(1,10));
        SendMessageA(sensitivity_slider, TBM_SETTICFREQ, 1, 0);
        SendMessageA(sensitivity_slider, TBM_SETPOS, TRUE, mouse_sensitivity);
        display_status_label = CreateWindowA("STATIC", "", WS_CHILD|WS_VISIBLE, 18, 430, 470, 42, hwnd, NULL, NULL, NULL);
        connect_button = CreateWindowA("BUTTON", "Connect / retry", WS_CHILD|WS_VISIBLE|WS_TABSTOP|BS_PUSHBUTTON, 18, 477, 470, 34, hwnd, (HMENU)1005, NULL, NULL);
        hotspot_button = CreateWindowA("BUTTON", "Open Windows Mobile Hotspot settings", WS_CHILD|WS_VISIBLE|WS_TABSTOP|BS_PUSHBUTTON, 18, 518, 470, 34, hwnd, (HMENU)1011, NULL, NULL);
        hotspot_info_label = CreateWindowA("STATIC", "Hotspot status and connected devices are managed by Windows. Set its band to 5 GHz if offered.", WS_CHILD|WS_VISIBLE, 18, 558, 470, 44, hwnd, NULL, NULL, NULL);
        update_buttons(); return 0;
    case WM_COMMAND:
        if (LOWORD(wp) == 1001) { capture_on = !capture_on; update_buttons(); }
        if (LOWORD(wp) == 1002) { input_on = !input_on; update_buttons(); }
        if (LOWORD(wp) == 1003) { mouse_mode = (mouse_mode + 1) % 4; save_settings(); update_buttons(); }
        if (LOWORD(wp) == 1004) { click_mode = (click_mode + 1) % 4; save_settings(); update_buttons(); }
        if (LOWORD(wp) == 1005) {
            if (ui_connected.load()) { disconnect_requested.store(true); set_text_if_changed(connect_button, "Disconnecting..."); EnableWindow(connect_button, FALSE); }
            else start_connect();
        }
        if (LOWORD(wp) == 1006) { bitrate_mode = (bitrate_mode + 1) % 3; save_settings(); reconnect_requested = true; update_buttons(); }
        if (LOWORD(wp) == 1008) pending_display_action.store(4);
        if (LOWORD(wp) == 1009) pending_display_action.store(2);
        if (LOWORD(wp) == 1010) { high_latency.store(!high_latency.load()); save_settings(); reconnect_requested.store(true); update_buttons(); }
        if (LOWORD(wp) == 1011) open_hotspot_settings();
        return 0;
    case WM_HSCROLL:
        if ((HWND)lp == sensitivity_slider) { mouse_sensitivity = (int)SendMessageA(sensitivity_slider, TBM_GETPOS, 0, 0); save_settings(); update_buttons(); }
        return 0;
    case WM_APP_SET_TEXT:
        set_text_if_changed((HWND)wp, (const char *)lp); delete[] (char *)lp; return 0;
    case WM_APP_DISPLAY_STATE:
        update_display_controls((unsigned)wp, (const char *)lp); delete[] (char *)lp; return 0;
    case WM_APP_CONNECTION_STATE:
        set_text_if_changed(connection_label, (const char *)lp);
        if (wp == 1) { ui_connected.store(true); set_text_if_changed(connect_button, "Disconnect"); EnableWindow(connect_button, TRUE); }
        else { ui_connected.store(false); set_text_if_changed(connect_button, wp == 2 ? "Searching..." : "Connect / retry"); EnableWindow(connect_button, wp != 2); }
        delete[] (char *)lp; return 0;
    case WM_APP_REFRESH_BUTTONS: update_buttons(); return 0;
    case WM_CLOSE: DestroyWindow(hwnd); return 0;
    case WM_DESTROY: window_closed.store(true); main_window = NULL; PostQuitMessage(0); return 0;
    }
    return DefWindowProcA(hwnd, msg, wp, lp);
}

static void open_gui(HINSTANCE instance) {
    INITCOMMONCONTROLSEX ic = { sizeof ic, ICC_BAR_CLASSES }; InitCommonControlsEx(&ic);
    WNDCLASSA wc = {}; wc.lpfnWndProc = window_proc; wc.hInstance = instance; wc.lpszClassName = "WupStreamHostWindow";
    wc.hCursor = LoadCursor(NULL, IDC_ARROW); wc.hbrBackground = (HBRUSH)(COLOR_WINDOW + 1);
    RegisterClassA(&wc);
    main_window = CreateWindowA(wc.lpszClassName, "WUP Stream Host", WS_OVERLAPPED|WS_CAPTION|WS_SYSMENU|WS_MINIMIZEBOX,
        CW_USEDEFAULT, CW_USEDEFAULT, 530, 660, NULL, NULL, instance, NULL);
    if (main_window) {
        ShowWindow(main_window, SW_SHOW); UpdateWindow(main_window);
        update_display_controls((display_backup_ready ? 1u : 0u) | (display_active ? 2u : 0u) | (display_pending ? 4u : 0u), display_status);
    }
}

static DWORD WINAPI gui_thread_proc(void *) {
    open_gui(GetModuleHandleA(NULL));
    if (gui_ready_event) SetEvent(gui_ready_event);
    MSG msg;
    while (GetMessageA(&msg, NULL, 0, 0) > 0) { TranslateMessage(&msg); DispatchMessageA(&msg); }
    return 0;
}

static void wait_until_qpc(LARGE_INTEGER deadline, LARGE_INTEGER frequency) {
    for (;;) {
        LARGE_INTEGER now; QueryPerformanceCounter(&now);
        LONGLONG left = deadline.QuadPart - now.QuadPart;
        if (left <= 0) return;
        if (left > frequency.QuadPart / 500) Sleep(1);
        else if (left > frequency.QuadPart / 3000) Sleep(0);
        else YieldProcessor();
    }
}

static void print_addresses() {
    char host[256] = {};
    if (gethostname(host, sizeof host) == 0) {
        struct addrinfo hints = {}, *res = NULL; hints.ai_family = AF_INET;
        if (getaddrinfo(host, NULL, &hints, &res) == 0) {
            puts("This PC's IPv4 addresses (use one if auto-discovery fails):");
            for (auto p = res; p; p = p->ai_next) {
                char ip[64]; DWORD n = sizeof ip;
                if (WSAAddressToStringA(p->ai_addr, (DWORD)p->ai_addrlen, NULL, ip, &n) == 0) {
                    char *port = strchr(ip, ':'); if (port) *port = 0;
                    printf("  %s\n", ip);
                    if (strlen(pc_addresses) > 10) strncat(pc_addresses, ", ", sizeof(pc_addresses)-strlen(pc_addresses)-1);
                    strncat(pc_addresses, ip, sizeof(pc_addresses)-strlen(pc_addresses)-1);
                }
            }
            freeaddrinfo(res);
        }
    }
}

struct DesktopCapture {
    HDC screen = NULL, memory = NULL;
    HBITMAP bitmap = NULL; HGDIOBJ original = NULL;
    int width = 0, height = 0;
    void close() {
        if (memory && original) SelectObject(memory, original);
        if (bitmap) DeleteObject(bitmap);
        if (memory) DeleteDC(memory);
        if (screen) ReleaseDC(NULL, screen);
        screen = memory = NULL; bitmap = NULL; original = NULL; width = height = 0;
    }
    bool open(int w, int h) {
        close(); screen = GetDC(NULL); if (!screen) return false;
        memory = CreateCompatibleDC(screen); bitmap = CreateCompatibleBitmap(screen, WUPSTREAM_W, WUPSTREAM_H);
        if (!memory || !bitmap) { close(); return false; }
        original = SelectObject(memory, bitmap); width = w; height = h;
        return original != NULL;
    }
    bool capture(uint8_t *out) {
        int sw = GetSystemMetrics(SM_CXSCREEN), sh = GetSystemMetrics(SM_CYSCREEN);
        if (!screen || !memory || !bitmap || width != sw || height != sh) if (!open(sw, sh)) return false;
        CURSORINFO ci = {}; ci.cbSize = sizeof ci; GetCursorInfo(&ci);
        SetStretchBltMode(memory, HALFTONE);
        bool ok = StretchBlt(memory, 0, 0, WUPSTREAM_W, WUPSTREAM_H, screen, 0, 0, sw, sh, SRCCOPY | CAPTUREBLT) != 0;
    if (ok && (ci.flags & CURSOR_SHOWING) && ci.hCursor && ci.ptScreenPos.x >= 0 && ci.ptScreenPos.x < sw && ci.ptScreenPos.y >= 0 && ci.ptScreenPos.y < sh) {
        ICONINFO ii = {};
        if (GetIconInfo(ci.hCursor, &ii)) {
            int cw = GetSystemMetrics(SM_CXCURSOR), ch = GetSystemMetrics(SM_CYCURSOR);
            int x = (ci.ptScreenPos.x - (int)ii.xHotspot) * WUPSTREAM_W / sw;
            int y = (ci.ptScreenPos.y - (int)ii.yHotspot) * WUPSTREAM_H / sh;
            int dw = cw * WUPSTREAM_W / sw, dh = ch * WUPSTREAM_H / sh;
            DrawIconEx(memory, x, y, ci.hCursor, dw, dh, 0, NULL, DI_NORMAL);
            if (ii.hbmMask) DeleteObject(ii.hbmMask);
            if (ii.hbmColor) DeleteObject(ii.hbmColor);
        }
    }
    BITMAPINFO bi = {}; bi.bmiHeader.biSize = sizeof(BITMAPINFOHEADER); bi.bmiHeader.biWidth = WUPSTREAM_W;
    bi.bmiHeader.biHeight = -WUPSTREAM_H; bi.bmiHeader.biPlanes = 1; bi.bmiHeader.biBitCount = 32; bi.bmiHeader.biCompression = BI_RGB;
        SelectObject(memory, original);
        if (ok) ok = GetDIBits(memory, bitmap, 0, WUPSTREAM_H, out, &bi, DIB_RGB_COLORS) != 0;
        SelectObject(memory, bitmap);
        return ok;
    }
};

struct Loopback {
    IMMDevice *device = NULL; IAudioClient *client = NULL; IAudioCaptureClient *capture = NULL;
    WAVEFORMATEX *fmt = NULL; bool ready = false;
    bool open() {
        IMMDeviceEnumerator *enumerator = NULL;
        HRESULT hr = CoCreateInstance(__uuidof(MMDeviceEnumerator), NULL, CLSCTX_ALL, __uuidof(IMMDeviceEnumerator), (void**)&enumerator);
        if (FAILED(hr)) return false;
        hr = enumerator->GetDefaultAudioEndpoint(eRender, eConsole, &device); enumerator->Release();
        if (FAILED(hr)) return false;
        if (FAILED(device->Activate(__uuidof(IAudioClient), CLSCTX_ALL, NULL, (void**)&client))) return false;
        if (FAILED(client->GetMixFormat(&fmt))) return false;
        REFERENCE_TIME dur = 10000000;
        if (FAILED(client->Initialize(AUDCLNT_SHAREMODE_SHARED, AUDCLNT_STREAMFLAGS_LOOPBACK, dur, 0, fmt, NULL))) return false;
        if (FAILED(client->GetService(__uuidof(IAudioCaptureClient), (void**)&capture))) return false;
        ready = SUCCEEDED(client->Start()); return ready;
    }
    void send(wupstream *pad) {
        if (!ready) return;
        UINT32 packets = 0;
        while (SUCCEEDED(capture->GetNextPacketSize(&packets)) && packets) {
            BYTE *data = NULL; UINT32 frames = 0; DWORD flags = 0;
            if (FAILED(capture->GetBuffer(&data, &frames, &flags, NULL, NULL))) break;
            int ch = fmt->nChannels; std::vector<int16_t> pcm((size_t)frames * 2);
            bool isfloat = fmt->wFormatTag == WAVE_FORMAT_IEEE_FLOAT ||
                (fmt->wFormatTag == WAVE_FORMAT_EXTENSIBLE && ((WAVEFORMATEXTENSIBLE*)fmt)->SubFormat.Data1 == WAVE_FORMAT_IEEE_FLOAT);
            int bits = fmt->wBitsPerSample;
            for (UINT32 f = 0; f < frames; ++f) for (int c = 0; c < 2; ++c) {
                int sc = c < ch ? c : 0; float v = 0;
                if (!(flags & AUDCLNT_BUFFERFLAGS_SILENT)) {
                    const BYTE *p = data + ((size_t)f * ch + sc) * (bits / 8);
                    if (isfloat) memcpy(&v, p, sizeof(float));
                    else if (bits == 16) { int16_t s; memcpy(&s, p, 2); v = s / 32768.0f; }
                    else if (bits == 32) { int32_t s; memcpy(&s, p, 4); v = s / 2147483648.0f; }
                }
                if (v > 1) v = 1;
                if (v < -1) v = -1;
                pcm[(size_t)f * 2 + c] = (int16_t)(v * 32767.0f);
            }
            if (fmt->nSamplesPerSec == 48000) wupstream_audio(pad, pcm.data(), (int)frames);
            else { /* nearest-neighbour rate conversion keeps loopback usable on non-48 kHz devices */
                UINT32 n = (UINT32)((uint64_t)frames * 48000 / fmt->nSamplesPerSec);
                std::vector<int16_t> converted((size_t)n * 2);
                for (UINT32 k = 0; k < n; ++k) { UINT32 q = (UINT32)((uint64_t)k * fmt->nSamplesPerSec / 48000); if (q >= frames) q = frames - 1; converted[2*k]=pcm[2*q]; converted[2*k+1]=pcm[2*q+1]; }
                if (n) wupstream_audio(pad, converted.data(), (int)n);
            }
            capture->ReleaseBuffer(frames);
        }
    }
    ~Loopback() { if (client && ready) client->Stop(); if (capture) capture->Release(); if (client) client->Release(); if (device) device->Release(); if (fmt) CoTaskMemFree(fmt); }
};

int main(int argc, char **argv) {
    WSADATA wd; WSAStartup(MAKEWORD(2,2), &wd); CoInitializeEx(NULL, COINIT_MULTITHREADED);
    load_settings();
    initialize_display_backup();
    connect_ip = argc > 1 ? argv[1] : NULL;
    puts("WUP Stream Windows host | F8 toggles desktop/audio | F9 toggles GamePad input | Esc exits");
    print_addresses();
    gui_ready_event = CreateEventA(NULL, TRUE, FALSE, NULL);
    gui_thread_handle = CreateThread(NULL, 0, gui_thread_proc, NULL, 0, NULL);
    if (!gui_thread_handle || WaitForSingleObject(gui_ready_event, 5000) != WAIT_OBJECT_0 || !main_window) {
        puts("Could not create the control window.");
        if (gui_thread_handle) { CloseHandle(gui_thread_handle); gui_thread_handle = NULL; }
        if (gui_ready_event) { CloseHandle(gui_ready_event); gui_ready_event = NULL; }
        if (display_active) restore_display();
        CoUninitialize(); WSACleanup(); return 1;
    }
    PostMessageA(main_window, WM_COMMAND, 1005, 0); /* auto-discover on the GUI thread */
    std::vector<uint8_t> buffers[2] = {
        std::vector<uint8_t>((size_t)WUPSTREAM_W * WUPSTREAM_H * 4),
        std::vector<uint8_t>((size_t)WUPSTREAM_W * WUPSTREAM_H * 4)
    };
    DesktopCapture desktop_capture;
    int front = 0; bool prevF8 = false, prevF9 = false;
    uint32_t previous = 0;
    LARGE_INTEGER qpc_frequency; QueryPerformanceFrequency(&qpc_frequency);
    const LONGLONG frame_ticks = (LONGLONG)(qpc_frequency.QuadPart / 59.94);
    wupstream *pad = NULL; Loopback *audio = NULL;
    LARGE_INTEGER next_frame = {}, last_input_tick = {};
    while (!window_closed) {
        if (window_closed || (GetAsyncKeyState(VK_ESCAPE) & 0x8000)) break;
        process_display_request();
        if (disconnect_requested.exchange(false) && pad) {
            for (int k=1;k<24;k++) if (previous & (1u<<k)) key(control_keys[k], false);
            previous = 0; sync_mouse_buttons(false, 0, false);
            wupstream_close(pad); pad = NULL; delete audio; audio = NULL;
            post_connection_update(false, "Disconnected by user.");
            continue;
        }
        bool f8 = (GetAsyncKeyState(VK_F8) & 0x8000) != 0, f9 = (GetAsyncKeyState(VK_F9) & 0x8000) != 0;
        bool hotkey_changed = false;
        if (f8 && !prevF8) { capture_on.store(!capture_on.load()); hotkey_changed = true; }
        if (f9 && !prevF9) { input_on.store(!input_on.load()); hotkey_changed = true; }
        prevF8 = f8; prevF9 = f9;
        if (hotkey_changed && main_window) PostMessageA(main_window, WM_APP_REFRESH_BUTTONS, 0, 0);

        if (reconnect_requested.load() && !connecting.load() && !connect_thread) {
            reconnect_requested.store(false);
            if (pad) {
                for (int k=1;k<24;k++) if (previous & (1u<<k)) key(control_keys[k], false);
                previous = 0; sync_mouse_buttons(false, 0, false);
                wupstream_close(pad); pad = NULL; delete audio; audio = NULL;
            }
            if (main_window) PostMessageA(main_window, WM_COMMAND, 1005, 0);
        }
        if (InterlockedCompareExchange(&connect_done, 0, 0)) {
            InterlockedExchange(&connect_done, 0);
            if (connect_thread) { WaitForSingleObject(connect_thread, INFINITE); CloseHandle(connect_thread); connect_thread = NULL; }
            connecting.store(false);
            if (reconnect_requested.load()) {
                reconnect_requested.store(false);
                if (connect_result) wupstream_close(connect_result);
                connect_result = NULL;
                if (main_window) PostMessageA(main_window, WM_COMMAND, 1005, 0);
                continue;
            }
            if (connect_result) {
                pad = connect_result; connect_result = NULL;
                char peer[16] = {};
                if (!wupstream_peer_ipv4(pad, peer, sizeof peer)) {
                    char status[128]; _snprintf(status, sizeof status, "Connected to GamePad at %s", peer);
                    post_connection_update(true, status);
                } else post_connection_update(true, "Connected to GamePad");
                puts("Connected to GamePad.");
                audio = new Loopback();
                if (audio->open()) puts("WASAPI system-audio loopback: ON");
                else puts("WASAPI loopback unavailable; streaming silence.");
                QueryPerformanceCounter(&next_frame); last_input_tick = next_frame;
            } else {
                post_connection_update(false, "No GamePad found. Check WUP Stream, Wi-Fi, and firewall; retry any time.");
                puts("No GamePad found. The control window remains available; press Connect / retry after opening WUP Stream.");
            }
        }

        if (!pad) { Sleep(10); continue; }
        wait_until_qpc(next_frame, qpc_frequency);
        if (window_closed || (GetAsyncKeyState(VK_ESCAPE) & 0x8000)) break;
        process_display_request();
        f8 = (GetAsyncKeyState(VK_F8) & 0x8000) != 0; f9 = (GetAsyncKeyState(VK_F9) & 0x8000) != 0;
        hotkey_changed = false;
        if (f8 && !prevF8) { capture_on.store(!capture_on.load()); hotkey_changed = true; }
        if (f9 && !prevF9) { input_on.store(!input_on.load()); hotkey_changed = true; }
        prevF8 = f8; prevF9 = f9;
        if (hotkey_changed && main_window) PostMessageA(main_window, WM_APP_REFRESH_BUTTONS, 0, 0);

        wupstream_input_t in;
        if (wupstream_input(pad, &in) != 0) {
            puts("GamePad disconnected.");
            for (int k=1;k<24;k++) if (previous & (1u<<k)) key(control_keys[k], false);
            previous = 0; sync_mouse_buttons(false, 0, false);
            wupstream_close(pad); pad = NULL; delete audio; audio = NULL;
            post_connection_update(false, "Disconnected. Press Connect / retry to reconnect.");
            continue;
        }
        LARGE_INTEGER input_tick; QueryPerformanceCounter(&input_tick);
        double input_dt = (double)(input_tick.QuadPart-last_input_tick.QuadPart) / qpc_frequency.QuadPart;
        last_input_tick = input_tick;
        if (input_on) {
            uint32_t mask = in.buttons & 0xffffu;
            if (mouse_mode == 3) mask &= ~(WUPSTREAM_LEFT | WUPSTREAM_RIGHT | WUPSTREAM_UP | WUPSTREAM_DOWN);
            if (click_mode == 1) mask &= ~(WUPSTREAM_A | WUPSTREAM_B);
            if (click_mode == 2 || click_mode == 3) mask &= ~(WUPSTREAM_ZL | WUPSTREAM_ZR);
            if (mouse_mode != 1) {
                if (in.ly > 350) mask |= 1u << 16;
                if (in.ly < -350) mask |= 1u << 17;
                if (in.lx < -350) mask |= 1u << 18;
                if (in.lx > 350) mask |= 1u << 19;
            }
            if (mouse_mode != 2) {
                if (in.ry > 350) mask |= 1u << 20;
                if (in.ry < -350) mask |= 1u << 21;
                if (in.rx < -350) mask |= 1u << 22;
                if (in.rx > 350) mask |= 1u << 23;
            }
            for (int k=1;k<24;k++) if (!!(mask & (1u<<k)) != !!(previous & (1u<<k))) key(control_keys[k], (mask & (1u<<k)) != 0);
            previous = mask;
            if (in.touched) move_mouse_from_touch(in);
            else move_mouse_from_stick(in, input_dt);
        }
        sync_mouse_buttons(in.touched != 0, in.buttons, input_on);
        int back = 1-front;
        if (!capture_on || !desktop_capture.capture(buffers[back].data())) memset(buffers[back].data(), 0, buffers[back].size());
        /* Publish only a fully captured back buffer. wupstream_frame copies the full image under its encoder lock
           before the sender can packetize the corresponding immutable slice/frame sequence. */
        front = back;
        if (wupstream_frame(pad, buffers[front].data(), WUPSTREAM_W*4, WUPSTREAM_BGRA)) {
            for (int k=1;k<24;k++) if (previous & (1u<<k)) key(control_keys[k], false);
            previous = 0; sync_mouse_buttons(false, 0, false);
            wupstream_close(pad); pad = NULL; delete audio; audio = NULL;
            post_connection_update(false, "Disconnected. Press Connect / retry to reconnect.");
            continue;
        }
        if (capture_on) audio->send(pad);
        else { static int16_t silence[1600] = {}; wupstream_audio(pad, silence, 800); }
        next_frame.QuadPart += frame_ticks;
        LARGE_INTEGER done; QueryPerformanceCounter(&done);
        while (next_frame.QuadPart <= done.QuadPart) next_frame.QuadPart += frame_ticks; /* fixed cadence; skip overdue slots, never burst */
    }
    for (int k=1;k<24;k++) if (previous & (1u<<k)) key(control_keys[k], false);
    sync_mouse_buttons(false, 0, false);
    desktop_capture.close();
    if (display_active) restore_display();
    if (pad) wupstream_close(pad);
    delete audio;
    if (connect_thread) {
        WaitForSingleObject(connect_thread, INFINITE); CloseHandle(connect_thread); connect_thread = NULL;
        if (connect_result) wupstream_close(connect_result);
    }
    if (gui_thread_handle) { WaitForSingleObject(gui_thread_handle, INFINITE); CloseHandle(gui_thread_handle); }
    if (gui_ready_event) CloseHandle(gui_ready_event);
    CoUninitialize(); WSACleanup(); return 0;
}
