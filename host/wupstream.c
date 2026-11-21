/* libwupstream: the PC side of wupstream's stream (protocol: pad/stream/stream.c). Video is x264 with the GamePad patch
 * (x264-drh-mode.patch: no slice headers, no planar prediction), set up as Sunshine for the GamePad did it, which
 * played on the real pad; each frame's slice data, without start code, NAL header and emulation prevention bytes,
 * goes in UDP packets straight into the pad's decoder ring. */
#include "wupstream.h"
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <x264.h>
#include <pthread.h>
#ifdef _WIN32
#include <winsock2.h>
#include <windows.h>
typedef int socklen_t;
static double now(void) { LARGE_INTEGER f, c; QueryPerformanceFrequency(&f); QueryPerformanceCounter(&c); return (double)c.QuadPart / f.QuadPart; }
static void nap(void) { Sleep(1); }
#else
#include <arpa/inet.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <sys/socket.h>
#include <time.h>
#include <unistd.h>
#define closesocket close
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + t.tv_nsec / 1e9; }
static void nap(void) { struct timespec t = { 0, 1000000 }; nanosleep(&t, 0); }
#endif

struct wupstream {
    int sock;
    struct sockaddr_in pad;
    x264_t *enc;
    x264_picture_t pic;
    uint32_t frame, aseq;
    int keyframe, gone, have;
    double last_in, last_hello, last_key, next;
    uint8_t report[128], *slices, apart[16];
    int napart, center[4];                                /* (the sticks at rest) */
    /* the pad's screen refresh, as it reports it: a recent refresh in our time, the period; a window of measurements */
    double vbase, vper, win_min, win_t0, phase, wait_t;
    int win_n, locked, wait_cur, wait_prev, skips, extra;
    pthread_t thread; pthread_mutex_t mu, packet_mu; pthread_cond_t cv;  /* packet_mu serializes complete video packet runs */
    double packet_last;
    int fresh, took, have_pic, quit, started, sent, repeats;
    struct { uint32_t frame; int len, idr; uint8_t *data; } kept[8];   /* the last frames, to send lost packets again */
    int resent, drop, packet_delay_us, cushion, rumble, rumble_sent, mic, light, light_pad;   /* pacing; light: 1..6 | keep << 7 */
    int16_t micbuf[48000]; int mic_w, mic_n;                 /* the last second of the microphone */            /* frames waiting on the pad: this refresh, the last */
};

static void put(wupstream *w, const void *d, int n) { sendto(w->sock, (const char *)d, n, 0, (struct sockaddr *)&w->pad, sizeof w->pad); }
/* The pad's screen refreshes every 16.683 ms on its own clock (59.94 Hz), and its decoder wants exactly one frame per
   refresh, at a steady point of it: frames that drift through the refresh tear at the top, and one that comes after a
   refresh went without stops the decoder (measured on the pad; Nintendo's driver locks the pad's screen to the console's
   frames instead: LVC 0x17cac). So every input packet says how long ago the pad's screen refreshed, and frames are sent
   in step with that. The network's delay only ever makes a measurement late: the earliest of each 64 counts. */
#define PERIOD 0.0166833
static void refresh_seen(wupstream *w, double t) {
    if (!w->vper) { w->vper = PERIOD; w->vbase = t; w->win_n = 0; }
    double e = fmod(t - w->vbase, w->vper);
    if (e > w->vper / 2) e -= w->vper;
    if (e < -w->vper / 2) e += w->vper;
    if (!w->win_n) { w->win_min = e; w->win_t0 = t; } else if (e < w->win_min) w->win_min = e;
    if (++w->win_n < 64) return;
    double periods = (t - w->win_t0) / w->vper;
    if (w->locked && periods > 4) w->vper += 0.1 * w->win_min / periods;      /* (its clock against ours) */
    if (w->vper < PERIOD * 0.998 || w->vper > PERIOD * 1.002) w->vper = PERIOD;
    w->vbase += w->win_min;
    w->vbase += floor((t - w->vbase) / w->vper) * w->vper;                     /* (kept near now) */
    w->win_n = 0; w->locked = 1;
}
static void send_packet(wupstream *w, int j, int q) {            /* packet q of kept frame j */
    if (w->packet_delay_us > 0 && w->packet_last > 0) {
        double due = w->packet_last + w->packet_delay_us / 1000000.0;
        while (now() < due) ;                                      /* a short precision wait avoids burst loss on the pad */
    }
    uint8_t pkt[16 + 1400] = { 'V', (uint8_t)w->kept[j].idr };
    int off = q * 1400, n = w->kept[j].len - off < 1400 ? w->kept[j].len - off : 1400;
    memcpy(pkt + 4, &w->kept[j].frame, 4); memcpy(pkt + 8, &off, 4); memcpy(pkt + 12, &w->kept[j].len, 4);
    memcpy(pkt + 16, w->kept[j].data + off, n);
    put(w, pkt, 16 + n);
    w->packet_last = now();
}
static void pump(wupstream *w) {                               /* what the pad sent; a hello now and then */
    uint8_t b[1100];
    struct sockaddr_in from; socklen_t fl = sizeof from;
    int n;
    while ((n = recvfrom(w->sock, (char *)b, sizeof b, 0, (struct sockaddr *)&from, &fl)) > 0) {
        if (from.sin_addr.s_addr != w->pad.sin_addr.s_addr) continue;
        if (b[0] == 'N' && n >= 4 + 8 * b[1]) {                      /* the pad lacks these packets: paced retransmission */
            pthread_mutex_lock(&w->packet_mu);
            for (int i = 0; i < b[1]; i++) {
                uint32_t f; memcpy(&f, b + 4 + 8 * i, 4);
                int k = b[8 + 8 * i] | b[9 + 8 * i] << 8, j = f % 8;
                if (w->kept[j].frame != f || !w->kept[j].data) continue;
                int npk = (w->kept[j].len + 1399) / 1400;
                for (int q = k == 0xffff ? 0 : k; q < (k == 0xffff ? npk : k + 1) && q < npk; q++) send_packet(w, j, q), w->resent++;
            }
            pthread_mutex_unlock(&w->packet_mu);
        }
        if (b[0] == 'M' && n > 8) for (int i = 8; i + 1 < n; i += 2) {   /* the microphone: 16-bit mono, 48 kHz */
            w->micbuf[w->mic_w] = (int16_t)(b[i] | b[i + 1] << 8); w->mic_w = (w->mic_w + 1) % 48000;
            if (w->mic_n < 48000) w->mic_n++;
        }
        if (b[0] == 'I' && n == 136) {
            memcpy(w->report, b + 8, 128); w->have = 1; w->last_in = now(); w->light_pad = b[4];
            refresh_seen(w, w->last_in - (b[2] | b[3] << 8) / 997300.0);   /* (ticks since its refresh: ~997.3 kHz) */
            if (b[1] & 1 && now() - w->last_key > 0.1) w->keyframe = 1;   /* (not the requests already on their way) */
            /* the fewest frames waiting on the pad during each whole refresh (wait_prev: the last whole one, -1: none yet) */
            if (w->last_in - w->wait_t > PERIOD) { w->wait_prev = w->wait_cur; w->wait_cur = 7; w->wait_t = w->last_in; }
            if ((b[1] >> 1 & 7) < w->wait_cur) w->wait_cur = b[1] >> 1 & 7;
        }
    }
    double t = now();
    if (t - w->last_hello > 0.25) { char h[4] = { 'H', 1, (char)w->mic, (char)w->light }; put(w, h, 4); w->last_hello = t; }
    if (w->have && t - w->last_in > 2 && !w->gone) { w->gone = 1; if (w->started) pthread_cond_broadcast(&w->cv); }     /* the pad stopped answering (or left the stream) */
}

static void *sender(void *arg);
wupstream *wupstream_open(const char *ip, int timeout_ms) {
#ifdef _WIN32
    WSADATA wd; WSAStartup(MAKEWORD(2, 2), &wd); timeBeginPeriod(1);
#endif
    wupstream *w = calloc(1, sizeof *w);
    pthread_mutex_init(&w->packet_mu, NULL);
    w->packet_delay_us = 200;
    w->sock = (int)socket(AF_INET, SOCK_DGRAM, 0);                   /* (its own port: several GamePads, several programs) */
    struct sockaddr_in me = { 0 };
    me.sin_family = AF_INET;
    if (bind(w->sock, (struct sockaddr *)&me, sizeof me)) { closesocket(w->sock); pthread_mutex_destroy(&w->packet_mu); free(w); return 0; }
#ifdef _WIN32
    u_long nb = 1; ioctlsocket(w->sock, FIONBIO, &nb);
#else
    fcntl(w->sock, F_SETFL, fcntl(w->sock, F_GETFL) | O_NONBLOCK);
#endif
    w->pad.sin_family = AF_INET; w->pad.sin_port = htons(50000);
    double end = now() + timeout_ms / 1000.0;
    if (ip) w->pad.sin_addr.s_addr = inet_addr(ip);
    else {                                                           /* the first GamePad that announces itself ('B', to port 50001) */
        int find = (int)socket(AF_INET, SOCK_DGRAM, 0), one = 1;
        setsockopt(find, SOL_SOCKET, SO_REUSEADDR, (const char *)&one, sizeof one);
#ifdef SO_REUSEPORT
        setsockopt(find, SOL_SOCKET, SO_REUSEPORT, (const char *)&one, sizeof one);   /* (other programs looking too) */
#endif
        me.sin_port = htons(50001);
#ifdef _WIN32
        ioctlsocket(find, FIONBIO, &nb);
#else
        fcntl(find, F_SETFL, fcntl(find, F_GETFL) | O_NONBLOCK);
#endif
        int ok = !bind(find, (struct sockaddr *)&me, sizeof me);
        while (ok && !w->pad.sin_addr.s_addr) {
            uint8_t b[16]; struct sockaddr_in from; socklen_t fl = sizeof from;
            if (recvfrom(find, (char *)b, sizeof b, 0, (struct sockaddr *)&from, &fl) >= 1 && b[0] == 'B') w->pad.sin_addr = from.sin_addr;
            else if (now() > end) ok = 0;
            else nap();
        }
        closesocket(find);
        if (!ok) { wupstream_close(w); return 0; }
    }
    while (!w->have || !w->locked) {                                 /* hello until it answers, and we know where its screen's refresh is */
        pump(w);
        if (now() > end) { wupstream_close(w); return 0; }
        nap();
    }
    x264_param_t p;
    x264_param_default_preset(&p, "veryfast", "zerolatency");
    static const char *drc[][2] = { { "drh-mode", "1" }, { "ref", "1" }, { "bframes", "0" }, { "cabac", "1" },
        { "constrained-intra", "1" }, { "intra-refresh", "0" }, { "weightp", "0" }, { "8x8dct", "0" },
        { "chroma-qp-offset", "0" }, { "mvrange", "64" }, { "partitions", "i4x4" }, { "scenecut", "0" },
        { "keyint", "infinite" }, { "slices", "1" }, { "sliced-threads", "0" }, { "threads", "1" }, { "aud", "0" },
        { "ipratio", "1.0" } };
    for (unsigned i = 0; i < sizeof drc / sizeof *drc; i++) x264_param_parse(&p, drc[i][0], drc[i][1]);
    /* constant quality (CRF), capped at 10 Mbps: above that frames get lost over the pad's Wi-Fi and its decoder falls
       behind (measured); a busy frame may borrow 3 frames' worth */
    int kbps = getenv("WUPSTREAM_KBPS") ? atoi(getenv("WUPSTREAM_KBPS")) : 10000;
    p.i_width = WUPSTREAM_W; p.i_height = WUPSTREAM_H; p.i_csp = X264_CSP_I420; p.i_fps_num = 60; p.i_fps_den = 1;
    p.rc.i_rc_method = X264_RC_CRF; p.rc.f_rf_constant = getenv("WUPSTREAM_CRF") ? (float)atof(getenv("WUPSTREAM_CRF")) : 18;
    p.rc.i_vbv_max_bitrate = kbps; p.rc.i_vbv_buffer_size = kbps / 60;
    p.i_log_level = getenv("WUPSTREAM_DEBUG") ? X264_LOG_INFO : X264_LOG_ERROR;
    if (getenv("WUPSTREAM_X264")) {                                  /* more x264 settings, "key=value:key=value" */
        char b[512]; snprintf(b, sizeof b, "%s", getenv("WUPSTREAM_X264"));
        for (char *t = strtok(b, ":"); t; t = strtok(NULL, ":")) { char *v = strchr(t, '='); if (v) *v++ = 0; x264_param_parse(&p, t, v ? v : "1"); }
    }
    x264_param_apply_profile(&p, "high");
    if (!(w->enc = x264_encoder_open(&p)) || x264_picture_alloc(&w->pic, X264_CSP_I420, WUPSTREAM_W, WUPSTREAM_H)) { wupstream_close(w); return 0; }
    w->slices = malloc(WUPSTREAM_W * WUPSTREAM_H * 2);
    w->keyframe = 1;
    w->drop = getenv("WUPSTREAM_DROP") ? atoi(getenv("WUPSTREAM_DROP")) : 0;
    w->packet_delay_us = getenv("WUPSTREAM_PACKET_DELAY_US") ? atoi(getenv("WUPSTREAM_PACKET_DELAY_US")) : 200;
    if (w->packet_delay_us < 0) w->packet_delay_us = 0;
    if (w->packet_delay_us > 5000) w->packet_delay_us = 5000;
    w->cushion = getenv("WUPSTREAM_HIGH_LATENCY") && atoi(getenv("WUPSTREAM_HIGH_LATENCY")) ? 4 : 2;
    w->phase = (getenv("WUPSTREAM_PHASE_MS") ? atof(getenv("WUPSTREAM_PHASE_MS")) : 3) / 1000;
    for (int i = 0; i < 4; i++) {                                    /* the sticks at rest (each pad is a little off) */
        int v = (w->report[6 + 2 * i] | w->report[7 + 2 * i] << 8) - 0x800;
        w->center[i] = v > -300 && v < 300 ? v : 0;
    }
    pthread_mutex_init(&w->mu, NULL); pthread_cond_init(&w->cv, NULL);
    w->started = !pthread_create(&w->thread, NULL, sender, w);
    if (!w->started) { wupstream_close(w); return 0; }
    return w;
}

int wupstream_input(wupstream *w, wupstream_input_t *in) {
    pthread_mutex_lock(&w->mu); pump(w); pthread_mutex_unlock(&w->mu);
    const uint8_t *r = w->report;
    memset(in, 0, sizeof *in);
    memcpy(in->report, r, 128);
    in->buttons = (r[2] << 8 | r[3]) & ~1u;                          /* (bit 0 is SYNC: the pad's, not ours) */
    if (r[0x50] & 0x80) in->buttons |= WUPSTREAM_L3;
    if (r[0x50] & 0x40) in->buttons |= WUPSTREAM_R3;
    if (r[0x50] & 0x20) in->buttons |= WUPSTREAM_TV;
    int *st[4] = { &in->lx, &in->ly, &in->rx, &in->ry };
    for (int i = 0; i < 4; i++) *st[i] = (r[6 + 2 * i] | r[7 + 2 * i] << 8) - 0x800 - w->center[i];
    for (int i = 0; i < 3; i++) {
        in->accel[i] = (int16_t)(r[15 + 2 * i] | r[16 + 2 * i] << 8);
        in->gyro[i] = (int32_t)((uint32_t)(r[21 + 3 * i] | r[22 + 3 * i] << 8 | r[23 + 3 * i] << 16) << 8) >> 8;
    }
    in->volume = r[14];
    in->backlight = w->light_pad;
    /* The battery: the report's byte 5 is the pad's own continuous reading, byte 4 its power flags (bit 0: plugged in, bit
       6: charging); the console draws its battery symbol from these (the pad's firmware only passes them on). The scale is
       from the thresholds in the pad's power controller firmware (UMI_ section: 9 sets of 5, the lowest steps at 136-141,
       the highest at 147-158); a full battery read 166 on the pad, and 12 more while charging. */
    int raw = r[5] - (r[4] & 0x40 ? 12 : 0);
    in->battery = !r[5] ? -1 : raw <= 136 ? 0 : raw >= 158 ? 100 : (raw - 136) * 100 / 22;
    in->charging = r[4] >> 6 & 1; in->plugged = r[4] & 1;
    int n = 0, sx = 0, sy = 0;                                       /* ten touch samples: x, y (bit 15 = valid) */
    for (int i = 0; i < 10; i++) {
        int x = r[36 + 4 * i] | r[37 + 4 * i] << 8, y = r[38 + 4 * i] | r[39 + 4 * i] << 8;
        if (x & y & 0x8000) { sx += x & 0xfff; sy += y & 0xfff; n++; }
    }
    if (n) {                                                         /* (calibration measured on the pad) */
        int x = (sx / n - 107) * WUPSTREAM_W / (3980 - 107), y = (3895 - sy / n) * WUPSTREAM_H / (3895 - 155);
        in->touched = 1; in->tx = x < 0 ? 0 : x >= WUPSTREAM_W ? WUPSTREAM_W - 1 : x; in->ty = y < 0 ? 0 : y >= WUPSTREAM_H ? WUPSTREAM_H - 1 : y;
    }
    return w->gone ? -1 : 0;
}

/* encode the picture in w->pic and send it at the next refresh slot */
static void send_picture(wupstream *w, int at_once) {
    /* one frame per refresh of the pad's screen, sent from a fixed point of it */
    double t2 = now();
    if (at_once) w->next = t2;
    else {
        double k = ceil((t2 + 0.004 - w->vbase - w->phase) / w->vper), slot = w->vbase + w->phase + k * w->vper;
        if (slot - w->next < w->vper * 0.5) slot += w->vper;         /* (never two in one refresh) */
        /* The pad's decoder starts at most one frame per refresh, so it never catches up by itself: when more than the
           cushion waited there through a whole refresh (a big frame took longer than one to decode), let a refresh pass.
           Never on older readings: that empties its queue. */
        if (w->wait_prev > w->cushion) { slot += w->vper; w->skips++; w->wait_prev = -1; w->wait_cur = 7; w->wait_t = slot; }
        w->next = slot;
        /* the program has until 5 ms before then to hand over its next picture (the encoder's time); else the last one again */
        while ((t2 = now()) < w->next - 0.005 && !w->quit) {
            pump(w);                                                     /* (what the pad says, as it comes: the timing is in it) */
            pthread_mutex_unlock(&w->mu);
            if (w->next - 0.005 - t2 > 0.002) nap();
            pthread_mutex_lock(&w->mu);
        }
    }
    w->took = w->fresh;
    double t = now();
    int key = w->keyframe && t - w->last_key > 0.25;                /* (asked for at 200 Hz while one is on its way) */
    w->pic.i_type = key ? X264_TYPE_IDR : X264_TYPE_AUTO; w->pic.i_pts = w->frame;
    if (key) { w->keyframe = 0; w->last_key = t; }
    static FILE *dump;
    if (!dump && getenv("WUPSTREAM_DUMP")) dump = fopen(getenv("WUPSTREAM_DUMP"), "wb");
    x264_nal_t *nal; int nn;
    x264_picture_t out;
    if (x264_encoder_encode(w->enc, &nal, &nn, &w->pic, &out) < 0) return;
    int len = 0, idr = 0;
    for (int i = 0; dump && i < nn; i++) fwrite(nal[i].p_payload, 1, nal[i].i_payload, dump);
    for (int i = 0; i < nn; i++) {                                   /* slices: payload only, unescaped */
        if (nal[i].i_type != NAL_SLICE && nal[i].i_type != NAL_SLICE_IDR) continue;
        idr |= nal[i].i_type == NAL_SLICE_IDR;
        const uint8_t *d = nal[i].p_payload;
        int n = nal[i].i_payload, s = d[2] == 1 ? 3 : 4, zeros = 0;
        for (int k = s + 1; k < n; k++) {
            if (zeros >= 2 && d[k] == 3) { zeros = 0; continue; }
            zeros = d[k] ? 0 : zeros + 1;
            w->slices[len++] = d[k];
        }
    }
    { int j = w->frame % 8;                                           /* immutable complete encoded frame; N can only ask for this sequence */
      uint8_t *d = realloc(w->kept[j].data, len ? len : 1);
      if (d) { memcpy(d, w->slices, len); w->kept[j].data = d; w->kept[j].frame = w->frame; w->kept[j].len = len; w->kept[j].idr = idr; }
      else { w->kept[j].frame = UINT32_MAX; w->kept[j].len = 0; } }
    if (w->took) { w->fresh = 0; w->sent++; pthread_cond_broadcast(&w->cv); } else if (!at_once) w->repeats++;   /* (the program goes on) */
    pthread_mutex_unlock(&w->mu);
    while ((t2 = now()) < w->next) if (w->next - t2 > 0.002) nap();
    if (w->rumble || w->rumble_sent) { char r[4] = { 'R', (char)w->rumble, 0, 0 }; put(w, r, 4); w->rumble_sent = w->rumble; }   /* (the motor stops 100 ms after the last "on") */
    /* spread over up to 4 ms: the pad's radio talks at 54 Mbit/s */
    double t0 = now(), span = 0.004 * (len + 1399) / 1400 / ((len + 1399) / 1400 + 1);
    int npk = (len + 1399) / 1400, j = w->frame % 8;
    pthread_mutex_lock(&w->packet_mu);                              /* no retransmit can split/interleave this frame */
    double last_packet = t0;
    for (int k = 0; k < npk; k++) {
        if (w->kept[j].frame != w->frame || !w->kept[j].data) break;
        double due = t0 + span * k / npk;
        double paced = last_packet + w->packet_delay_us / 1000000.0;
        if (paced > due) due = paced;
        while (now() < due) ;                                        /* precise sub-ms pacing; avoid coarse Sleep jitter */
        if (w->drop && rand() % w->drop == 0) continue;              /* (WUPSTREAM_DROP: a test of the pad asking again) */
        send_packet(w, j, k);
        last_packet = now();
    }
    pthread_mutex_unlock(&w->packet_mu);
    pthread_mutex_lock(&w->mu);
    w->frame++;
    if (idr) w->extra = w->cushion;
}
/* The sender. The pad's decoder stops for good when a refresh comes and it has no frame queued (measured: every second
   or third time). So (1) a cushion of frames is kept waiting on the pad: after every keyframe the same picture goes
   w->cushion more times at the following refreshes, and (2) every refresh gets a frame: the program's new picture, or,
   when it has none in time (it hitched, or runs at 30 a second), the last one again. */
static void *sender(void *arg) {
    wupstream *w = arg;
    pthread_mutex_lock(&w->mu);
    while (!w->quit) {
        pump(w);
        if (!w->have_pic || w->gone) { pthread_mutex_unlock(&w->mu); nap(); pthread_mutex_lock(&w->mu); continue; }
        send_picture(w, 0);
        while (w->extra > 0 && !w->quit) { w->extra--; send_picture(w, 0); }
    }
    pthread_mutex_unlock(&w->mu);
    return NULL;
}

int wupstream_frame(wupstream *w, const void *pixels, int stride, int format) {
    /* One atomic source frame: hold mu through the complete RGBA->I420 copy. The sender encodes under the same lock,
       copies the finished slice bytes into kept[frame % 8], then packetizes that immutable, monotonically numbered frame. */
    pthread_mutex_lock(&w->mu);
    while (w->fresh && !w->gone) pthread_cond_wait(&w->cv, &w->mu);  /* (the one before is on its way: one per refresh) */
    if (w->gone) { pthread_mutex_unlock(&w->mu); return -1; }
    const uint8_t *px = pixels;
    int ri = format == WUPSTREAM_BGRA ? 2 : 0, bi = 2 - ri;
    uint8_t *Y = w->pic.img.plane[0], *U = w->pic.img.plane[1], *V = w->pic.img.plane[2];
    for (int y = 0; y < WUPSTREAM_H; y++)                                 /* RGB -> I420 (BT.601, limited range) */
        for (int x = 0; x < WUPSTREAM_W; x++) {
            const uint8_t *p = px + y * stride + x * 4;
            int r = p[ri], g = p[1], b = p[bi];
            Y[y * w->pic.img.i_stride[0] + x] = (uint8_t)(((66 * r + 129 * g + 25 * b + 128) >> 8) + 16);
            if (!(x & 1) && !(y & 1)) {
                U[y / 2 * w->pic.img.i_stride[1] + x / 2] = (uint8_t)(((-38 * r - 74 * g + 112 * b + 128) >> 8) + 128);
                V[y / 2 * w->pic.img.i_stride[2] + x / 2] = (uint8_t)(((112 * r - 94 * g - 18 * b + 128) >> 8) + 128);
            }
        }
    w->fresh = w->have_pic = 1;
    while (w->fresh && !w->gone) pthread_cond_wait(&w->cv, &w->mu);  /* until it has gone out: this paces the program */
    int r = w->gone ? -1 : 0;
    pthread_mutex_unlock(&w->mu);
    return r;
}

int wupstream_audio(wupstream *w, const int16_t *lr, int frames) {
    pthread_mutex_lock(&w->mu); pump(w); pthread_mutex_unlock(&w->mu);
    if (w->gone) return -1;
    pthread_mutex_lock(&w->packet_mu);                 /* keep audio datagrams out of a video frame's packet run */
    const uint8_t *src = (const uint8_t *)lr;
    int n = frames * 4;
    uint8_t pkt[8 + 1408] = { 'A' };
    while (w->napart + n >= 16) {                                    /* whole 16-byte blocks, up to 1408 bytes each */
        int take = (w->napart + n) / 16 * 16;
        if (take > 1408) take = 1408;
        memcpy(pkt + 4, &w->aseq, 4); w->aseq++;
        memcpy(pkt + 8, w->apart, w->napart);
        memcpy(pkt + 8 + w->napart, src, take - w->napart);
        src += take - w->napart; n -= take - w->napart; w->napart = 0;
        if (w->packet_delay_us > 0 && w->packet_last > 0) {
            double due = w->packet_last + w->packet_delay_us / 1000000.0;
            while (now() < due) ;                                  /* pace audio datagrams too; avoid short bursts */
        }
        put(w, pkt, 8 + take); w->packet_last = now();
    }
    memcpy(w->apart + w->napart, src, n); w->napart += n;
    pthread_mutex_unlock(&w->packet_mu);
    return 0;
}

int wupstream_mic(wupstream *w, int16_t *samples, int max) {
    pthread_mutex_lock(&w->mu);
    if (!w->mic) { w->mic = 1; w->last_hello = 0; }                  /* (asked for with the next hello) */
    pump(w);
    int n = w->mic_n < max ? w->mic_n : max;
    for (int i = 0; i < n; i++) samples[i] = w->micbuf[(w->mic_w + 48000 - w->mic_n + i) % 48000];
    w->mic_n -= n;
    pthread_mutex_unlock(&w->mu);
    return n;
}

void wupstream_backlight(wupstream *w, int level, int keep) {
    if (level > 6) level = 6;
    pthread_mutex_lock(&w->mu); w->light = level < 1 ? 0x40 : level | (keep ? 0x80 : 0); w->last_hello = 0; pthread_mutex_unlock(&w->mu);
}

void wupstream_rumble(wupstream *w, int on) {
    pthread_mutex_lock(&w->mu);
    if (w->rumble != (on != 0)) { char r[4] = { 'R', (char)(on != 0), 0, 0 }; put(w, r, 4); }   /* at once; the sender says it again with every frame */
    w->rumble = on != 0;
    pthread_mutex_unlock(&w->mu);
}

int wupstream_peer_ipv4(wupstream *w, char *out, int out_size) {
    if (!w || !out || out_size < 16) return -1;
    const unsigned char *a = (const unsigned char *)&w->pad.sin_addr.s_addr;
    int n = snprintf(out, (size_t)out_size, "%u.%u.%u.%u", a[0], a[1], a[2], a[3]);
    return n > 0 && n < out_size ? 0 : -1;
}

void wupstream_close(wupstream *w) {
    if (!w) return;
    if (w->started) {
        pthread_mutex_lock(&w->mu); w->quit = 1; pthread_cond_broadcast(&w->cv); pthread_mutex_unlock(&w->mu);
        pthread_join(w->thread, NULL);
    }
    if (w->pad.sin_addr.s_addr) for (int i = 0; i < 3; i++) put(w, "Q", 1);
    if (getenv("WUPSTREAM_DEBUG")) fprintf(stderr, "wupstream: %u frames, %d refreshes skipped for the pad's decoder, refresh %.3f ms, %d refreshes filled with the last picture again, %d packets sent again\n", w->frame, w->skips, w->vper * 1000, w->repeats, w->resent);
    if (w->enc) { x264_picture_clean(&w->pic); x264_encoder_close(w->enc); }
    for (int i = 0; i < 8; i++) free(w->kept[i].data);
    closesocket(w->sock); free(w->slices); pthread_mutex_destroy(&w->packet_mu); free(w);
}
