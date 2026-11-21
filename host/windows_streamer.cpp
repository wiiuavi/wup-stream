/* Windows desktop/audio streamer for libwupstream. */
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <winsock2.h>
#include <ws2tcpip.h>
#include <mmdeviceapi.h>
#include <audioclient.h>
#include <functiondiscoverykeys_devpkey.h>
#include <stdint.h>
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
static HWND main_window = NULL, capture_button = NULL, input_button = NULL;
static HWND mouse_button = NULL, click_button = NULL;
static bool capture_on = true, input_on = true, window_closed = false;
static char pc_addresses[512] = "PC IPv4: ";
static int mouse_mode = 0, click_mode = 0;
static char settings_path[MAX_PATH] = {};
static bool sent_left = false, sent_right = false;

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
    int xaxis = mouse_mode == 1 ? in.lx : in.rx;
    int yaxis = mouse_mode == 1 ? in.ly : in.ry;
    if (abs(xaxis) < 90) xaxis = 0;
    if (abs(yaxis) < 90) yaxis = 0;
    if (!xaxis && !yaxis) return;
    POINT p; if (!GetCursorPos(&p)) return;
    const double speed = 1200.0;
    p.x += (int)(xaxis / 1100.0 * speed * dt);
    p.y -= (int)(yaxis / 1100.0 * speed * dt);
    int maxx = GetSystemMetrics(SM_CXSCREEN)-1, maxy = GetSystemMetrics(SM_CYSCREEN)-1;
    if (p.x < 0) p.x = 0;
    if (p.x > maxx) p.x = maxx;
    if (p.y < 0) p.y = 0;
    if (p.y > maxy) p.y = maxy;
    SetCursorPos(p.x, p.y);
}
static void move_mouse_from_touch(const wupstream_input_t &in) {
    int width = GetSystemMetrics(SM_CXSCREEN), height = GetSystemMetrics(SM_CYSCREEN);
    SetCursorPos(in.tx * (width-1) / (WUPSTREAM_W-1), in.ty * (height-1) / (WUPSTREAM_H-1));
}

static const char *mouse_mode_name() { return mouse_mode == 1 ? "left joystick" : mouse_mode == 2 ? "right joystick" : "none"; }
static const char *click_mode_name() { return click_mode == 1 ? "A/B" : click_mode == 2 ? "triggers" : click_mode == 3 ? "triggers inverted" : "none"; }
static void save_settings() {
    if (!settings_path[0]) return;
    char value[16]; _snprintf(value, sizeof value, "%d", mouse_mode); WritePrivateProfileStringA("Input", "MouseControl", value, settings_path);
    _snprintf(value, sizeof value, "%d", click_mode); WritePrivateProfileStringA("Input", "ClickMapping", value, settings_path);
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
    if (mouse_mode < 0 || mouse_mode > 2) mouse_mode = 0;
    if (click_mode < 0 || click_mode > 3) click_mode = 0;
}

static void update_buttons() {
    if (capture_button) SetWindowTextA(capture_button, capture_on ? "Desktop + audio: ON  (F8)" : "Desktop + audio: OFF  (F8)");
    if (input_button) SetWindowTextA(input_button, input_on ? "GamePad input: ON  (F9)" : "GamePad input: OFF  (F9)");
    if (mouse_button) { char text[128]; _snprintf(text, sizeof text, "Mouse control: %s  (click to cycle)", mouse_mode_name()); SetWindowTextA(mouse_button, text); }
    if (click_button) { char text[128]; _snprintf(text, sizeof text, "Mouse clicks: %s  (click to cycle)", click_mode_name()); SetWindowTextA(click_button, text); }
}

static LRESULT CALLBACK window_proc(HWND hwnd, UINT msg, WPARAM wp, LPARAM lp) {
    switch (msg) {
    case WM_CREATE:
        CreateWindowA("STATIC", pc_addresses, WS_CHILD|WS_VISIBLE, 18, 18, 360, 30, hwnd, NULL, NULL, NULL);
        capture_button = CreateWindowA("BUTTON", "", WS_CHILD|WS_VISIBLE|WS_TABSTOP|BS_PUSHBUTTON, 18, 56, 350, 38, hwnd, (HMENU)1001, NULL, NULL);
        input_button = CreateWindowA("BUTTON", "", WS_CHILD|WS_VISIBLE|WS_TABSTOP|BS_PUSHBUTTON, 18, 106, 350, 38, hwnd, (HMENU)1002, NULL, NULL);
        mouse_button = CreateWindowA("BUTTON", "", WS_CHILD|WS_VISIBLE|WS_TABSTOP|BS_PUSHBUTTON, 18, 156, 350, 38, hwnd, (HMENU)1003, NULL, NULL);
        click_button = CreateWindowA("BUTTON", "", WS_CHILD|WS_VISIBLE|WS_TABSTOP|BS_PUSHBUTTON, 18, 206, 350, 38, hwnd, (HMENU)1004, NULL, NULL);
        update_buttons(); return 0;
    case WM_COMMAND:
        if (LOWORD(wp) == 1001) { capture_on = !capture_on; update_buttons(); }
        if (LOWORD(wp) == 1002) { input_on = !input_on; update_buttons(); }
        if (LOWORD(wp) == 1003) { mouse_mode = (mouse_mode + 1) % 3; save_settings(); update_buttons(); }
        if (LOWORD(wp) == 1004) { click_mode = (click_mode + 1) % 4; save_settings(); update_buttons(); }
        return 0;
    case WM_CLOSE: DestroyWindow(hwnd); return 0;
    case WM_DESTROY: window_closed = true; main_window = NULL; return 0;
    }
    return DefWindowProcA(hwnd, msg, wp, lp);
}

static void open_gui(HINSTANCE instance) {
    WNDCLASSA wc = {}; wc.lpfnWndProc = window_proc; wc.hInstance = instance; wc.lpszClassName = "WupStreamHostWindow";
    wc.hCursor = LoadCursor(NULL, IDC_ARROW); wc.hbrBackground = (HBRUSH)(COLOR_WINDOW + 1);
    RegisterClassA(&wc);
    main_window = CreateWindowA(wc.lpszClassName, "WUP Stream Host", WS_OVERLAPPED|WS_CAPTION|WS_SYSMENU|WS_MINIMIZEBOX,
        CW_USEDEFAULT, CW_USEDEFAULT, 405, 300, NULL, NULL, instance, NULL);
    if (main_window) { ShowWindow(main_window, SW_SHOW); UpdateWindow(main_window); }
}

static void pump_window() {
    MSG msg;
    while (PeekMessageA(&msg, NULL, 0, 0, PM_REMOVE)) { TranslateMessage(&msg); DispatchMessageA(&msg); }
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

static bool screen_frame(uint8_t *out) {
    int sw = GetSystemMetrics(SM_CXSCREEN), sh = GetSystemMetrics(SM_CYSCREEN);
    HDC src = GetDC(NULL), dst = CreateCompatibleDC(src);
    HBITMAP bmp = CreateCompatibleBitmap(src, WUPSTREAM_W, WUPSTREAM_H);
    if (!src || !dst || !bmp) { if (bmp) DeleteObject(bmp); if (dst) DeleteDC(dst); if (src) ReleaseDC(NULL, src); return false; }
    HGDIOBJ old = SelectObject(dst, bmp);
    SetStretchBltMode(dst, HALFTONE);
    bool ok = StretchBlt(dst, 0, 0, WUPSTREAM_W, WUPSTREAM_H, src, 0, 0, sw, sh, SRCCOPY | CAPTUREBLT) != 0;
    BITMAPINFO bi = {}; bi.bmiHeader.biSize = sizeof(BITMAPINFOHEADER); bi.bmiHeader.biWidth = WUPSTREAM_W;
    bi.bmiHeader.biHeight = -WUPSTREAM_H; bi.bmiHeader.biPlanes = 1; bi.bmiHeader.biBitCount = 32; bi.bmiHeader.biCompression = BI_RGB;
    SelectObject(dst, old);
    if (ok) ok = GetDIBits(dst, bmp, 0, WUPSTREAM_H, out, &bi, DIB_RGB_COLORS) != 0;
    DeleteObject(bmp); DeleteDC(dst); ReleaseDC(NULL, src); return ok;
}

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
    puts("WUP Stream Windows host | F8 toggles desktop/audio capture | F9 toggles controller forwarding | Esc exits");
    print_addresses(); puts("Waiting for the GamePad (open WUP Stream on it; same Wi-Fi network)...");
    wupstream *pad = wupstream_open(argc > 1 ? argv[1] : NULL, 30000);
    if (!pad) { puts("No GamePad connected. Check the IP/firewall and try again."); CoUninitialize(); WSACleanup(); return 1; }
    puts("Connected. Desktop is scaled to 854x480. F8 capture: ON; F9 controller: ON.");
    open_gui(GetModuleHandleA(NULL));
    Loopback audio; if (audio.open()) puts("WASAPI system-audio loopback: ON"); else puts("WASAPI loopback unavailable; continuing with silent audio.");
    std::vector<uint8_t> buffers[2] = {
        std::vector<uint8_t>((size_t)WUPSTREAM_W * WUPSTREAM_H * 4),
        std::vector<uint8_t>((size_t)WUPSTREAM_W * WUPSTREAM_H * 4)
    };
    int front = 0;
    bool video = true, controls = true, prevF8 = false, prevF9 = false;
    uint32_t previous = 0;
    LARGE_INTEGER qpc_frequency, next_frame, last_input_tick; QueryPerformanceFrequency(&qpc_frequency); QueryPerformanceCounter(&next_frame); last_input_tick = next_frame;
    const LONGLONG frame_ticks = (LONGLONG)(qpc_frequency.QuadPart / 59.94);
    wupstream_input_t in;
    for (;;) {
        wait_until_qpc(next_frame, qpc_frequency);
        pump_window();
        if (window_closed || (GetAsyncKeyState(VK_ESCAPE) & 0x8000)) break;
        if (wupstream_input(pad, &in) != 0) break;
        bool f8 = (GetAsyncKeyState(VK_F8) & 0x8000) != 0, f9 = (GetAsyncKeyState(VK_F9) & 0x8000) != 0;
        if (f8 && !prevF8) capture_on = !capture_on;
        if (f9 && !prevF9) {
            input_on = !input_on;
        }
        if (capture_on != video) { video = capture_on; printf("Desktop/audio capture: %s\n", video ? "ON" : "OFF"); }
        if (input_on != controls) {
            controls = input_on; printf("Controller forwarding: %s\n", controls ? "ON" : "OFF");
            if (!controls) {
                for (int k=1;k<24;k++) if (previous & (1u<<k)) key(control_keys[k], false);
                previous=0;
            }
        }
        update_buttons();
        prevF8 = f8; prevF9 = f9;
        LARGE_INTEGER input_tick; QueryPerformanceCounter(&input_tick);
        double input_dt = (double)(input_tick.QuadPart-last_input_tick.QuadPart) / qpc_frequency.QuadPart;
        last_input_tick = input_tick;
        if (controls) {
            uint32_t mask = in.buttons & 0xffffu;
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
        sync_mouse_buttons(in.touched != 0, in.buttons, controls);
        int back = 1-front;
        if (!video || !screen_frame(buffers[back].data())) memset(buffers[back].data(), 0, buffers[back].size());
        /* Publish only a fully captured back buffer. wupstream_frame copies the full image under its encoder lock
           before the sender can packetize the corresponding immutable slice/frame sequence. */
        front = back;
        if (wupstream_frame(pad, buffers[front].data(), WUPSTREAM_W*4, WUPSTREAM_BGRA)) break;
        if (video) audio.send(pad);
        else { static int16_t silence[1600] = {}; wupstream_audio(pad, silence, 800); }
        QueryPerformanceCounter(&next_frame);
        next_frame.QuadPart += frame_ticks;
        LARGE_INTEGER done; QueryPerformanceCounter(&done);
        if (next_frame.QuadPart <= done.QuadPart) next_frame.QuadPart = done.QuadPart + frame_ticks; /* never catch up in a burst */
    }
    for (int k=1;k<24;k++) if (previous & (1u<<k)) key(control_keys[k], false);
    sync_mouse_buttons(false, 0, false);
    wupstream_close(pad); CoUninitialize(); WSACleanup(); return 0;
}
