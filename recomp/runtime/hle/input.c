// Controller input: SDL keyboard/gamepad -> nn::hid Npad state.
//
// Both go through the player's bindings (runtime/hle/bindings.c, defaults there: keyboard WASD left stick, arrows
// d-pad, K/J/L/I = A/B/X/Y, Q/E = L/R, 1/3 = ZL/ZR, Enter / Backspace = Plus / Minus, numpad 8/4/5/6 right stick;
// controller by position, Switch A = east).
#include <pthread.h>
#include <SDL3/SDL.h>
#include <ctype.h>
#include <math.h>
#include <stdatomic.h>
#include <stdlib.h>
#include <string.h>

// === COMPATIBILIDAD TOUCHPAD PS4 (OPENORBIS) ===
#ifdef __ORBIS__
#include <orbisPad.h>
static float ps4_cursor_x = 960.0f; // Centrado en pantalla 1080p
static float ps4_cursor_y = 540.0f;
static float ps4_sensibilidad = 1.5f;
#endif
// ===============================================

#include "../hle.h"
#include "../nvn/nvn.h"
#include "../nvn/renderer.h"
#include "../settings.h"
#include "../input_bind.h"
#include "../padscript.h"

enum {
    BTN_A = 0, BTN_B, BTN_X, BTN_Y, BTN_LSTICK, BTN_RSTICK, BTN_L, BTN_R, BTN_ZL, BTN_ZR, BTN_PLUS, BTN_MINUS,
    BTN_LEFT, BTN_UP, BTN_RIGHT, BTN_DOWN
};

_Static_assert(BTN_DOWN == BIND_DOWN && BTN_ZL == BIND_ZL, "bindings follow the button bits");

static _Atomic uint64_t key_buttons, pad_buttons;
static _Atomic int32_t key_lx, key_ly, key_rx, key_ry, pad_lx, pad_ly, pad_rx, pad_ry;
static uint8_t keys_down[SDL_SCANCODE_COUNT];
static SDL_Gamepad *pad;
static _Atomic int64_t sampling;

// Players 2-4 (local multiplayer: Play Together): each further controller is the next player, Npad No. 2..4 (ids
// 1..3), through the same controller bindings. Player 1 keeps the keyboard, the on-screen controller and the first
// controller. LARECOMP_INPUT2 (same form as LARECOMP_INPUT) is a scripted player 2 for tests.
#define EXTRA_PADS 3
static SDL_Gamepad *extra_pad[EXTRA_PADS];
static _Atomic uint64_t extra_buttons[EXTRA_PADS];
static _Atomic int32_t extra_lx[EXTRA_PADS], extra_ly[EXTRA_PADS], extra_rx[EXTRA_PADS], extra_ry[EXTRA_PADS];
static _Atomic uint64_t script2_buttons;
static _Atomic int32_t script2_lx, script2_ly;
static bool script2_on(void) {
    static int on = -1;
    if (on < 0) on = getenv("LARECOMP_INPUT2") != NULL;
    return on;
}
static bool extra_connected(int i) { return extra_pad[i] || (i == 0 && script2_on()); }
static void style_changed(void);
static bool real_gamepad(SDL_JoystickID id);

// Host keys / buttons held by a test script (LARECOMP_HOST_INPUT, input_frame): they go through the bindings
static uint8_t test_keys[SDL_SCANCODE_COUNT];
static _Atomic uint32_t test_pad;
static _Atomic int32_t test_lx, test_ly;  // (a resting stick's drift: "lstick" in LARECOMP_HOST_INPUT)
static bool host_test;  // (then a real controller is left out: the player's own pad must not spoil the test)

static int held_key(int sc) { return sc > 0 && sc < SDL_SCANCODE_COUNT && (keys_down[sc] || test_keys[sc]); }

// Through the bindings (runtime/hle/bindings.c: g_bind_key), read on every key event, so a rebind applies at once.
static void recompute_keyboard(void) {
    uint64_t b = 0;
    for (int i = 0; i < BIND_PAD_COUNT; i++)
        if (held_key(g_bind_key[i])) b |= 1ull << i;
    key_buttons = b;
    key_lx = (held_key(g_bind_key[BIND_LS_RIGHT]) - held_key(g_bind_key[BIND_LS_LEFT])) * 32767;
    key_ly = (held_key(g_bind_key[BIND_LS_UP]) - held_key(g_bind_key[BIND_LS_DOWN])) * 32767;
    key_rx = (held_key(g_bind_key[BIND_RS_RIGHT]) - held_key(g_bind_key[BIND_RS_LEFT])) * 32767;
    key_ry = (held_key(g_bind_key[BIND_RS_UP]) - held_key(g_bind_key[BIND_RS_DOWN])) * 32767;
}

// Controller buttons (and the triggers as buttons) -> Switch buttons through g_bind_pad; the sticks stay the sticks.
static void recompute_pad(void) {
    uint32_t host = test_pad;
    if (pad && !host_test) {
        for (int i = 0; i < SDL_GAMEPAD_BUTTON_COUNT; i++)
            if (SDL_GetGamepadButton(pad, (SDL_GamepadButton)i)) host |= 1u << i;
        if (SDL_GetGamepadAxis(pad, SDL_GAMEPAD_AXIS_LEFT_TRIGGER) > 16000) host |= 1u << PADB_LTRIGGER;
        if (SDL_GetGamepadAxis(pad, SDL_GAMEPAD_AXIS_RIGHT_TRIGGER) > 16000) host |= 1u << PADB_RTRIGGER;
    }
    uint64_t b = 0;
    for (int i = 0; i < BIND_PAD_COUNT; i++)
        if (g_bind_pad[i] >= 0 && g_bind_pad[i] < PADB_HOST_COUNT && (host >> g_bind_pad[i] & 1)) b |= 1ull << i;
    pad_buttons = b;
    if (!pad || host_test) { pad_lx = test_lx, pad_ly = test_ly, pad_rx = pad_ry = 0; return; }
    pad_lx = SDL_GetGamepadAxis(pad, SDL_GAMEPAD_AXIS_LEFTX);
    pad_ly = -SDL_GetGamepadAxis(pad, SDL_GAMEPAD_AXIS_LEFTY);
    pad_rx = SDL_GetGamepadAxis(pad, SDL_GAMEPAD_AXIS_RIGHTX);
    pad_ry = -SDL_GetGamepadAxis(pad, SDL_GAMEPAD_AXIS_RIGHTY);
}

static void recompute_extra(int i) {
    SDL_Gamepad *g = extra_pad[i];
    uint32_t host = 0;
    if (g) {
        for (int k = 0; k < SDL_GAMEPAD_BUTTON_COUNT; k++)
            if (SDL_GetGamepadButton(g, (SDL_GamepadButton)k)) host |= 1u << k;
        if (SDL_GetGamepadAxis(g, SDL_GAMEPAD_AXIS_LEFT_TRIGGER) > 16000) host |= 1u << PADB_LTRIGGER;
        if (SDL_GetGamepadAxis(g, SDL_GAMEPAD_AXIS_RIGHT_TRIGGER) > 16000) host |= 1u << PADB_RTRIGGER;
    }
    uint64_t b = 0;
    for (int k = 0; k < BIND_PAD_COUNT; k++)
        if (g_bind_pad[k] >= 0 && g_bind_pad[k] < PADB_HOST_COUNT && (host >> g_bind_pad[k] & 1)) b |= 1ull << k;
    extra_buttons[i] = b;
    extra_lx[i] = g ? SDL_GetGamepadAxis(g, SDL_GAMEPAD_AXIS_LEFTX) : 0;
    extra_ly[i] = g ? -SDL_GetGamepadAxis(g, SDL_GAMEPAD_AXIS_LEFTY) : 0;
    extra_rx[i] = g ? SDL_GetGamepadAxis(g, SDL_GAMEPAD_AXIS_RIGHTX) : 0;
    extra_ly[i] = g ? -SDL_GetGamepadAxis(g, SDL_GAMEPAD_AXIS_RIGHTY) : 0;
}

static void open_extra(SDL_JoystickID id) {
    if ((pad && SDL_GetGamepadID(pad) == id) || !real_gamepad(id)) return;
    for (int i = 0; i < EXTRA_PADS; i++)
        if (extra_pad[i] && SDL_GetGamepadID(extra_pad[i]) == id) return;
    for (int i = 0; i < EXTRA_PADS; i++)
        if (!extra_pad[i]) {
            extra_pad[i] = SDL_OpenGamepad(id);
            if (!extra_pad[i]) return;
            LOG("[input] player %d: %s\n", i + 2, SDL_GetGamepadName(extra_pad[i]));
            recompute_extra(i);
            style_changed();
            return;
        }
}

static bool pads_from_p2(void) { return g_settings.pads_from_p2; }
static void note_family(void);
static bool scanned;

void input_pads_reassign(void) {
    if (pad) SDL_CloseGamepad(pad), pad = NULL;
    for (int i = 0; i < EXTRA_PADS; i++)
        if (extra_pad[i]) {
            SDL_CloseGamepad(extra_pad[i]);
            extra_pad[i] = NULL;
            recompute_extra(i);
        }
    style_changed();
    note_family();
    recompute_pad();
    scanned = false;
}

void input_reset(void) {
    memset(keys_down, 0, sizeof keys_down);
    recompute_keyboard();
}

volatile int g_debug_frame_request;

#define TEST_DEVICE 0x7E57u
static bool test_event(const SDL_Event *e) {
    switch (e->type) {
    case SDL_EVENT_KEY_DOWN: case SDL_EVENT_KEY_UP: return e->key.which == TEST_DEVICE;
    case SDL_EVENT_TEXT_INPUT: return e->text.windowID == TEST_DEVICE;
    case SDL_EVENT_GAMEPAD_BUTTON_DOWN: case SDL_EVENT_GAMEPAD_BUTTON_UP: return e->gbutton.which == TEST_DEVICE;
    case SDL_EVENT_MOUSE_MOTION: return e->motion.which == SDL_TOUCH_MOUSEID && e->motion.windowID == TEST_DEVICE;
    case SDL_EVENT_MOUSE_BUTTON_DOWN: case SDL_EVENT_MOUSE_BUTTON_UP:
        return e->button.which == SDL_TOUCH_MOUSEID && e->button.windowID == TEST_DEVICE;
    default: return false;
    }
}

bool input_user_blocked(const SDL_Event *e) {
    static int on = -1;
    if (on < 0) {
        const char *v = getenv("LARECOMP_NO_USER_INPUT");
        on = v ? atoi(v) != 0 : (getenv("LARECOMP_INPUT") || getenv("LARECOMP_DOORJUMP_TEST") || getenv("LARECOMP_PLACE") ||
                                 getenv("LARECOMP_HOST_INPUT") || getenv("LARECOMP_BIND_TEST") || padscript_active());
        if (on) LOG("[input] scripted run: keyboard, mouse and controllers ignored\n");
    }
    if (!on) return false;
    if (test_event(e)) return false;
    switch (e->type) {
    case SDL_EVENT_KEY_DOWN: case SDL_EVENT_KEY_UP: case SDL_EVENT_TEXT_INPUT: case SDL_EVENT_TEXT_EDITING:
    case SDL_EVENT_MOUSE_MOTION: case SDL_EVENT_MOUSE_BUTTON_DOWN: case SDL_EVENT_MOUSE_BUTTON_UP:
    case SDL_EVENT_MOUSE_WHEEL:
    case SDL_EVENT_GAMEPAD_ADDED: case SDL_EVENT_GAMEPAD_AXIS_MOTION: case SDL_EVENT_GAMEPAD_BUTTON_DOWN:
    case SDL_EVENT_GAMEPAD_BUTTON_UP: case SDL_EVENT_JOYSTICK_ADDED: case SDL_EVENT_JOYSTICK_AXIS_MOTION:
    case SDL_EVENT_JOYSTICK_BUTTON_DOWN: case SDL_EVENT_JOYSTICK_BUTTON_UP:
        return true;
    default:
        return false;
    }
}

static _Atomic int pad_family;
static _Atomic bool pad_connected;
static void note_family(void) {
    pad_connected = pad != NULL;
    int f = 0;
    if (pad) switch (SDL_GetGamepadType(pad)) {
        case SDL_GAMEPAD_TYPE_XBOX360: case SDL_GAMEPAD_TYPE_XBOXONE: f = 1; break;
        case SDL_GAMEPAD_TYPE_PS3: case SDL_GAMEPAD_TYPE_PS4: case SDL_GAMEPAD_TYPE_PS5: f = 2; break;
        default: break;
    }
    if (f != pad_family) LOG("[input] button prompts: %s controller\n", f == 1 ? "Xbox" : f == 2 ? "PlayStation" : "Nintendo / other");
    pad_family = f;
}
int input_pad_family(void) {
    static int env = -2;
    if (env == -2) {
        const char *e = getenv("LARECOMP_PAD_TYPE");
        env = !e ? -1 : !strcmp(e, "xbox") ? 1 : !strcmp(e, "playstation") || !strcmp(e, "ps") ? 2 : 0;
    }
    return env >= 0 ? env : pad_family;
}

bool input_gamepad_connected(void) { return pad_connected; }

static bool real_gamepad(SDL_JoystickID id) {
#ifdef __ANDROID__
    const char *n = SDL_GetGamepadNameForID(id);
    if (n && !strcmp(n, "qwerty2")) return false;
#else
    (void)id;
#endif
    return true;
}

static bool pc_event(const SDL_Event *e) {
    extern bool game_pc_key(int scancode, bool cmd, bool shift, bool down, bool repeat);
    extern bool game_pc_mouse(int button, int act, float x, float y);
    extern bool game_pc_wheel(float dx, float dy, bool shift);
    static bool taken[SDL_SCANCODE_COUNT];
    switch (e->type) {
    case SDL_EVENT_KEY_DOWN: case SDL_EVENT_KEY_UP: {
        int sc = e->key.scancode;
        if (sc <= 0 || sc >= SDL_SCANCODE_COUNT) return false;
        bool down = e->type == SDL_EVENT_KEY_DOWN;
        if (!down) {
            if (!taken[sc]) return false;
            taken[sc] = false;
            game_pc_key(sc, false, false, false, false);
            return true;
        }
#ifdef __APPLE__
        bool cmd = (e->key.mod & SDL_KMOD_GUI) != 0;
#else
        bool cmd = (e->key.mod & SDL_KMOD_CTRL) != 0;
#endif
        if (!game_pc_key(sc, cmd, (e->key.mod & SDL_KMOD_SHIFT) != 0, true, e->key.repeat)) return false;
        taken[sc] = true;
        return true;
    }
    case SDL_EVENT_MOUSE_BUTTON_DOWN: case SDL_EVENT_MOUSE_BUTTON_UP: case SDL_EVENT_MOUSE_MOTION: {
        if (e->button.which == SDL_TOUCH_MOUSEID) return false;
        int b = e->type == SDL_EVENT_MOUSE_MOTION
                    ? (e->motion.state & SDL_BUTTON_RMASK ? 3 : e->motion.state & SDL_BUTTON_MMASK ? 2 : 0)
                    : e->button.button == SDL_BUTTON_RIGHT ? 3 : e->button.button == SDL_BUTTON_MIDDLE ? 2 : 0;
        if (!b) return false;
        SDL_Window *w = SDL_GetWindowFromID(e->type == SDL_EVENT_MOUSE_MOTION ? e->motion.windowID : e->button.windowID);
        int ww = 1, wh = 1;
        if (w) SDL_GetWindowSize(w, &ww, &wh);
        float x = e->type == SDL_EVENT_MOUSE_MOTION ? e->motion.x : e->button.x;
        float y = e->type == SDL_EVENT_MOUSE_MOTION ? e->motion.y : e->button.y;
        return game_pc_mouse(b, e->type == SDL_EVENT_MOUSE_BOTTOM_DOWN ? 0 : e->type == SDL_EVENT_MOUSE_MOTION ? 1 : 2,
                             x / (ww > 0 ? ww : 1), y / (wh > 0 ? wh : 1));
    }
    case SDL_EVENT_MOUSE_WHEEL:
        return game_pc_wheel(e->wheel.x, e->wheel.y, (SDL_GetModState() & SDL_KMOD_SHIFT) != 0);
    default:
        return false;
    }
}

void input_handle_event(const SDL_Event *e) {
    extern bool touchpad_handle_event(const SDL_Event *e);
    extern bool touch_handle_event(const SDL_Event *e);
    extern bool menu_input_captured(void);
    
    // === LÓGICA DE DETECCIÓN DEL TOUCHPAD DE PS4 ===
    #ifdef __ORBIS__
    OrbisPadTouchData touch_data;
    if (orbisPadGetTouchData(0, &touch_data) == 0 && touch_data.fingerCount > 0) {
        ps4_cursor_x += touch_data.points.x * ps4_sensibilidad;
        ps4_cursor_y += touch_data.points.y * ps4_sensibilidad;
        
        if (ps4_cursor_x < 0) ps4_cursor_x = 0;
        if (ps4_cursor_x > 1920) ps4_cursor_x = 1920;
        if (ps4_cursor_y < 0) ps4_cursor_y = 0;
        if (ps4_cursor_y > 1080) ps4_cursor_y = 1080;

        SDL_Event fake_touch_event;
        fake_touch_event.type = SDL_EVENT_FINGER_MOTION;
        fake_touch_event.tfinger.x = ps4_cursor_x / 1920.0f;
        fake_touch_event.tfinger.y = ps4_cursor_y / 1080.0f;
        
        if (touch_handle_event(&fake_touch_event)) return;
    }
    #endif
    // ===============================================

    if (menu_input_captured()) switch (e->type) {
        case SDL_EVENT_FINGER_DOWN: case SDL_EVENT_FINGER_MOTION:
        case SDL_EVENT_MOUSE_BUTTON_DOWN: case SDL_EVENT_MOUSE_MOTION: case SDL_EVENT_MOUSE_WHEEL:
            return;
        default: break;
    }
    if (touchpad_handle_event(e) || touch_handle_event(e)) return;
    if (pc_event(e)) return;
    if (!scanned) {
        scanned = true;
        int n = 0;
        SDL_JoystickID *ids = SDL_GetGamepads(&n);
        if (n > 0 && !pad && !pads_from_p2() && real_gamepad(ids)) { pad = SDL_OpenGamepad(ids); LOG("[input] gamepad: %s\n", SDL_GetGamepadName(pad)); note_family(); }
        for (int i = pad ? 1 : 0; i < n; i++) open_extra(ids[i]);
        SDL_free(ids);
    }
    switch (e->type) {
    case SDL_EVENT_KEY_DOWN: case SDL_EVENT_KEY_UP:
        if (e->type == SDL_EVENT_KEY_DOWN && e->key.scancode == SDL_SCANCODE_F9 && !e->key.repeat) g_debug_frame_request = 1;
        if (e->key.scancode < SDL_SCANCODE_COUNT) keys_down[e->key.scancode] = e->type == SDL_EVENT_KEY_DOWN;
        recompute_keyboard();
        break;
    case SDL_EVENT_GAMEPAD_ADDED:
        if (!pad && !pads_from_p2() && real_gamepad(e->gdevice.which)) { pad = SDL_OpenGamepad(e->gdevice.which); LOG("[input] gamepad: %s\n", SDL_GetGamepadName(pad)); note_family(); }
        else open_extra(e->gdevice.which);
        break;
    case SDL_EVENT_GAMEPAD_REMOVED:
        if (pad && SDL_GetGamepadID(pad) == e->gdevice.which) { SDL_CloseGamepad(pad); pad = NULL; note_family(); }
        for (int i = 0; i < EXTRA_PADS; i++)
            if (extra_pad[i] && SDL_GetGamepadID(extra_pad[i]) == e->gdevice.which) {
                LOG("[input] player %d: controller removed\n", i + 2);
                SDL_CloseGamepad(extra_pad[i]);
                extra_pad[i] = NULL;
                recompute_extra(i);
                style_changed();
            }
        recompute_pad();
        break;
    case SDL_EVENT_GAMEPAD_AXIS_MOTION: case SDL_EVENT_GAMEPAD_BUTTON_DOWN: case SDL_EVENT_GAMEPAD_BUTTON_UP:
        recompute_pad();
        for (int i = 0; i < EXTRA_PADS; i++)
            if (extra_pad[i]) recompute_extra(i);
        break;
    }
}

static _Atomic uint64_t script_buttons;
static _Atomic int32_t script_lx, script_ly, script_rx, script_ry;

static void push_key(SDL_Scancode sc, SDL_Keymod mod, bool down) {
    SDL_Event e;
    memset(&e, 0, sizeof e);
    e.type = down ? SDL_EVENT_KEY_DOWN : SDL_EVENT_KEY_UP;
    e.key.which = TEST_DEVICE, e.key.scancode = sc, e.key.mod = mod, e.key.down = down;
    e.key.key = SDL_GetKeyFromScancode(sc, mod, false);
    SDL_PushEvent(&e);
}

void input_test_key(const char *name, bool down) { push_key(SDL_GetScancodeFromName(name), SDL_KMOD_NONE, down); }

static void *kbd_test_thread(void *arg) {
    extern int menu_keyboard_run(const char *initial, int max_len, char *out, int cap);
    char text[256] = "";
    int ok = menu_keyboard_run((const char *)arg, 32, text, sizeof text);
    LOG("[input] test keyboard: %s \"%s\"\n", ok ? "entered" : "cancelled", text);
    return NULL;
}

static void test_push(uint64_t frame, unsigned long start, unsigned long len) {
    // Implementacion interna de empuje de scripts de testeo
}
