// SPDX-FileCopyrightText: 2002-2025 PCSX2 Dev Team
// SPDX-License-Identifier: GPL-3.0+

#include "GS/Renderers/Common/GSDevice.h"
#include "Config.h"
#include "Counters.h"
#include "GS/GS.h"
#include "Host.h"
#include "IconsFontAwesome6.h"
#include "ImGui/FullscreenUI.h"
#include "ImGui/ImGuiFullscreen.h"
#include "ImGui/ImGuiManager.h"
#include "ImGui/ImGuiOverlays.h"
#include "Input/InputManager.h"
#include "MTGS.h"
#include "PerformanceMetrics.h"
#include "Recording/InputRecording.h"
#include "VMManager.h"

#include "common/FileSystem.h"
#include "common/Easing.h"
#include "common/StringUtil.h"
#include "common/Path.h"
#include "common/Timer.h"

#include "fmt/format.h"
#include "imgui.h"
#include "imgui_freetype.h"
#include "imgui_internal.h"
#include "common/Image.h"

#include <chrono>
#include <cmath>
#include <deque>
#include <mutex>
#include <unordered_map>

namespace ImGuiManager
{
	struct SoftwareCursor
	{
		std::string image_path;
		std::unique_ptr<GSTexture> texture;
		u32 color;
		float scale;
		float extent_x;
		float extent_y;
		std::pair<float, float> pos;
	};

	static void UpdateScale();
	static void SetStyle();
	static void SetKeyMap();
	static bool LoadFontData();
	static void UnloadFontData();
	static bool AddImGuiFonts();
	static ImFont* AddTextFont();
	static ImFont* AddFixedFont();
	static bool AddIconFonts();
	static bool AddEmojiFont();
	static void AcquirePendingOSDMessages(Common::Timer::Value current_time);
	static void DrawOSDMessages(Common::Timer::Value current_time);
	static void CreateSoftwareCursorTextures();
	static void UpdateSoftwareCursorTexture(u32 index);
	static void DestroySoftwareCursorTextures();
	static void DrawSoftwareCursor(const SoftwareCursor& sc, const std::pair<float, float>& pos);
	static void DrawSoftwareCursors();
} // namespace ImGuiManager

static float s_global_scale = 1.0f;

static std::string s_font_path;

static ImFont* s_standard_font;
static ImFont* s_fixed_font;

static std::vector<u8> s_standard_font_data;
static std::vector<u8> s_fixed_font_data;
static std::vector<u8> s_emoji_font_data;
static std::vector<u8> s_icon_fa_font_data;
static std::vector<u8> s_icon_pf_font_data;

static float s_window_width;
static float s_window_height;
static Common::Timer s_last_render_time;

// cached copies of WantCaptureKeyboard/Mouse, used to know when to dispatch events
static std::atomic_bool s_imgui_wants_keyboard{false};
static std::atomic_bool s_imgui_wants_mouse{false};
static std::atomic_bool s_imgui_wants_text{false};

static bool s_gamepad_swap_noth_west = false;

// mapping of host key -> imgui key
static std::unordered_map<u32, ImGuiKey> s_imgui_key_map;

static constexpr float OSD_FADE_IN_TIME = 0.1f;
static constexpr float OSD_FADE_OUT_TIME = 0.4f;

// need to keep track of this, so we can reinitialize on renderer switch
static bool s_fullscreen_ui_was_initialized = false;
static bool s_scale_changed = false;

static std::array<ImGuiManager::SoftwareCursor, InputManager::MAX_SOFTWARE_CURSORS> s_software_cursors = {};

void ImGuiManager::SetFontPath(std::string path)
{
	if (s_font_path == path)
		return;

	s_font_path = std::move(path);
	s_standard_font_data = {};

	if (ImGui::GetCurrentContext())
	{
		ImGui::EndFrame();

		if (!LoadFontData())
			pxFailRel("Failed to load font data");

		if (!AddImGuiFonts())
			pxFailRel("Failed to create ImGui font text");

		NewFrame();
	}
}

bool ImGuiManager::Initialize()
{
	if (!LoadFontData())
	{
		pxFailRel("Failed to load font data");
		return false;
	}

	s_global_scale = std::max(0.5f, g_gs_device->GetWindowScale() * (GSConfig.OsdScale / 100.0f));
	s_scale_changed = false;

	ImGuiContext& g = *ImGui::CreateContext();

	ImGuiIO& io = ImGui::GetIO();
	io.IniFilename = nullptr;
	io.BackendFlags |= ImGuiBackendFlags_RendererHasVtxOffset | ImGuiBackendFlags_RendererHasTextures | ImGuiBackendFlags_HasGamepad;
	io.ConfigFlags |= ImGuiConfigFlags_NavEnableKeyboard | ImGuiConfigFlags_NavEnableGamepad;
	io.KeyRepeatDelay = 0.5f;

	g.ConfigNavWindowingKeyNext = ImGuiKey_None;
	g.ConfigNavWindowingKeyPrev = ImGuiKey_None;
	g.ConfigNavWindowingWithGamepad = false;

	s_window_width = static_cast<float>(g_gs_device->GetWindowWidth());
	s_window_height = static_cast<float>(g_gs_device->GetWindowHeight());
	io.DisplayFramebufferScale = ImVec2(1, 1); // We already scale things ourselves, this would double-apply scaling
	io.DisplaySize = ImVec2(s_window_width, s_window_height);

	SetKeyMap();
	SetStyle();

	const bool add_fullscreen_fonts = s_fullscreen_ui_was_initialized;
	pxAssertRel(!FullscreenUI::IsInitialized(), "Fullscreen UI is not initialized on ImGui init");
	if (add_fullscreen_fonts)
	{
		ImGuiFullscreen::UpdateLayoutScale();
		ImGuiFullscreen::UpdateFontScale();
	}

	if (!AddImGuiFonts())
	{
		Host::ReportErrorAsync("ImGuiManager", "Failed to create ImGui font text");
		ImGui::DestroyContext();
		UnloadFontData();
		return false;
	}

	NewFrame();

	// reinitialize fsui if it was previously enabled
	if (add_fullscreen_fonts)
		InitializeFullscreenUI();

	CreateSoftwareCursorTextures();
	return true;
}

bool ImGuiManager::InitializeFullscreenUI()
{
	s_fullscreen_ui_was_initialized = !ImGui::GetCurrentContext() || FullscreenUI::Initialize();
	return s_fullscreen_ui_was_initialized;
}

void ImGuiManager::Shutdown(bool clear_state)
{
	DestroySoftwareCursorTextures();

	FullscreenUI::Shutdown(clear_state);
	ImGuiFullscreen::SetFont(nullptr);
	SaveStateSelectorUI::DestroyTextures();
	if (clear_state)
		s_fullscreen_ui_was_initialized = false;

	g_gs_device->DestroyImGuiTextures();

	if (ImGui::GetCurrentContext())
		ImGui::DestroyContext();

	s_standard_font = nullptr;
	s_fixed_font = nullptr;

	if (clear_state)
		UnloadFontData();
}

float ImGuiManager::GetWindowWidth()
{
	return s_window_width;
}

float ImGuiManager::GetWindowHeight()
{
	return s_window_height;
}

void ImGuiManager::WindowResized()
{
	const u32 new_width = g_gs_device ? g_gs_device->GetWindowWidth() : 0;
	const u32 new_height = g_gs_device ? g_gs_device->GetWindowHeight() : 0;

	s_window_width = static_cast<float>(new_width);
	s_window_height = static_cast<float>(new_height);
	ImGui::GetIO().DisplaySize = ImVec2(s_window_width, s_window_height);

	// Scale might have changed as a result of window resize.
	RequestScaleUpdate();
}

void ImGuiManager::RequestScaleUpdate()
{
	if (s_window_width > 0 && s_window_height > 0)
		s_scale_changed = true;
}

void ImGuiManager::UpdateScale()
{
	const float window_scale = g_gs_device ? g_gs_device->GetWindowScale() : 1.0f;
	const float scale = std::max(window_scale * (EmuConfig.GS.OsdScale / 100.0f), 0.5f);

	if ((!ImGuiFullscreen::UpdateLayoutScale()) && scale == s_global_scale)
		return;

	s_global_scale = scale;
	SetStyle();

	ImGuiFullscreen::UpdateFontScale();

	if (FullscreenUI::IsInitialized())
		FullscreenUI::ReloadSvgResources();
}

void ImGuiManager::NewFrame()
{
	ImGuiIO& io = ImGui::GetIO();
	io.DeltaTime = s_last_render_time.GetTimeSecondsAndReset();

	if (s_scale_changed)
	{
		s_scale_changed = false;
		UpdateScale();
	}

	ImGui::NewFrame();

	// Disable nav input on the implicit (Debug##Default) window. Otherwise we end up requesting keyboard
	// focus when there's nothing there. We use GetCurrentWindowRead() because otherwise it'll make it visible.
	ImGui::GetCurrentWindowRead()->Flags |= ImGuiWindowFlags_NoNavInputs;
	s_imgui_wants_keyboard.store(io.WantCaptureKeyboard, std::memory_order_relaxed);
	s_imgui_wants_mouse.store(io.WantCaptureMouse, std::memory_order_release);

	const bool want_text_input = io.WantTextInput;
	if (s_imgui_wants_text.load(std::memory_order_relaxed) != want_text_input)
	{
		s_imgui_wants_text.store(want_text_input, std::memory_order_release);
		if (want_text_input)
			Host::BeginTextInput();
		else
			Host::EndTextInput();
	}
}

void ImGuiManager::SkipFrame()
{
	ImGui::EndFrame();
	NewFrame();
}

void ImGuiManager::SetStyle()
{
	ImGuiStyle& style = ImGui::GetStyle();
	style = ImGuiStyle();
	style.WindowMinSize = ImVec2(1.0f, 1.0f);

	ImVec4* colors = style.Colors;
	colors[ImGuiCol_Text] = ImVec4(0.95f, 0.96f, 0.98f, 1.00f);
	colors[ImGuiCol_TextDisabled] = ImVec4(0.36f, 0.42f, 0.47f, 1.00f);
	colors[ImGuiCol_WindowBg] = ImVec4(0.11f, 0.15f, 0.17f, 1.00f);
	colors[ImGuiCol_ChildBg] = ImVec4(0.15f, 0.18f, 0.22f, 1.00f);
	colors[ImGuiCol_PopupBg] = ImVec4(0.08f, 0.08f, 0.08f, 0.94f);
	colors[ImGuiCol_Border] = ImVec4(0.08f, 0.10f, 0.12f, 1.00f);
	colors[ImGuiCol_BorderShadow] = ImVec4(0.00f, 0.00f, 0.00f, 0.00f);
	colors[ImGuiCol_FrameBg] = ImVec4(0.20f, 0.25f, 0.29f, 1.00f);
	colors[ImGuiCol_FrameBgHovered] = ImVec4(0.12f, 0.20f, 0.28f, 1.00f);
	colors[ImGuiCol_FrameBgActive] = ImVec4(0.09f, 0.12f, 0.14f, 1.00f);
	colors[ImGuiCol_TitleBg] = ImVec4(0.09f, 0.12f, 0.14f, 0.65f);
	colors[ImGuiCol_TitleBgActive] = ImVec4(0.08f, 0.10f, 0.12f, 1.00f);
	colors[ImGuiCol_TitleBgCollapsed] = ImVec4(0.00f, 0.00f, 0.00f, 0.51f);
	colors[ImGuiCol_MenuBarBg] = ImVec4(0.15f, 0.18f, 0.22f, 1.00f);
	colors[ImGuiCol_ScrollbarBg] = ImVec4(0.02f, 0.02f, 0.02f, 0.39f);
	colors[ImGuiCol_ScrollbarGrab] = ImVec4(0.20f, 0.25f, 0.29f, 1.00f);
	colors[ImGuiCol_ScrollbarGrabHovered] = ImVec4(0.18f, 0.22f, 0.25f, 1.00f);
	colors[ImGuiCol_ScrollbarGrabActive] = ImVec4(0.09f, 0.21f, 0.31f, 1.00f);
	colors[ImGuiCol_CheckMark] = ImVec4(0.28f, 0.56f, 1.00f, 1.00f);
	colors[ImGuiCol_SliderGrab] = ImVec4(0.28f, 0.56f, 1.00f, 1.00f);
	colors[ImGuiCol_SliderGrabActive] = ImVec4(0.37f, 0.61f, 1.00f, 1.00f);
	colors[ImGuiCol_Button] = ImVec4(0.20f, 0.25f, 0.29f, 1.00f);
	colors[ImGuiCol_ButtonHovered] = ImVec4(0.33f, 0.38f, 0.46f, 1.00f);
	colors[ImGuiCol_ButtonActive] = ImVec4(0.27f, 0.32f, 0.38f, 1.00f);
	colors[ImGuiCol_Header] = ImVec4(0.20f, 0.25f, 0.29f, 0.55f);
	colors[ImGuiCol_HeaderHovered] = ImVec4(0.33f, 0.38f, 0.46f, 1.00f);
	colors[ImGuiCol_HeaderActive] = ImVec4(0.27f, 0.32f, 0.38f, 1.00f);
	colors[ImGuiCol_Separator] = ImVec4(0.20f, 0.25f, 0.29f, 1.00f);
	colors[ImGuiCol_SeparatorHovered] = ImVec4(0.33f, 0.38f, 0.46f, 1.00f);
	colors[ImGuiCol_SeparatorActive] = ImVec4(0.27f, 0.32f, 0.38f, 1.00f);
	colors[ImGuiCol_ResizeGrip] = ImVec4(0.26f, 0.59f, 0.98f, 0.25f);
	colors[ImGuiCol_ResizeGripHovered] = ImVec4(0.33f, 0.38f, 0.46f, 1.00f);
	colors[ImGuiCol_ResizeGripActive] = ImVec4(0.27f, 0.32f, 0.38f, 1.00f);
	colors[ImGuiCol_Tab] = ImVec4(0.11f, 0.15f, 0.17f, 1.00f);
	colors[ImGuiCol_TabHovered] = ImVec4(0.33f, 0.38f, 0.46f, 1.00f);
	colors[ImGuiCol_TabSelected] = ImVec4(0.27f, 0.32f, 0.38f, 1.00f);
	colors[ImGuiCol_TabDimmed] = ImVec4(0.11f, 0.15f, 0.17f, 1.00f);
	colors[ImGuiCol_TabDimmedSelected] = ImVec4(0.11f, 0.15f, 0.17f, 1.00f);
	colors[ImGuiCol_PlotLines] = ImVec4(0.61f, 0.61f, 0.61f, 1.00f);
	colors[ImGuiCol_PlotLinesHovered] = ImVec4(1.00f, 0.43f, 0.35f, 1.00f);
	colors[ImGuiCol_PlotHistogram] = ImVec4(0.90f, 0.70f, 0.00f, 1.00f);
	colors[ImGuiCol_PlotHistogramHovered] = ImVec4(1.00f, 0.60f, 0.00f, 1.00f);
	colors[ImGuiCol_TextSelectedBg] = ImVec4(0.26f, 0.59f, 0.98f, 0.35f);
	colors[ImGuiCol_DragDropTarget] = ImVec4(1.00f, 1.00f, 0.00f, 0.90f);
	colors[ImGuiCol_NavCursor] = ImVec4(0.26f, 0.59f, 0.98f, 1.00f);
	colors[ImGuiCol_NavWindowingHighlight] = ImVec4(1.00f, 1.00f, 1.00f, 0.70f);
	colors[ImGuiCol_NavWindowingDimBg] = ImVec4(0.80f, 0.80f, 0.80f, 0.20f);
	colors[ImGuiCol_ModalWindowDimBg] = ImVec4(0.80f, 0.80f, 0.80f, 0.35f);

	style.ScaleAllSizes(s_global_scale);
}

void ImGuiManager::SetKeyMap()
{
	struct KeyMapping
	{
		ImGuiKey index;
		const char* name;
		const char* alt_name;
	};

	static constexpr KeyMapping mapping[] = {{ImGuiKey_LeftArrow, "Left"}, {ImGuiKey_RightArrow, "Right"}, {ImGuiKey_UpArrow, "Up"},
		{ImGuiKey_DownArrow, "Down"}, {ImGuiKey_PageUp, "PageUp"}, {ImGuiKey_PageDown, "PageDown"}, {ImGuiKey_Home, "Home"},
		{ImGuiKey_End, "End"}, {ImGuiKey_Insert, "Insert"}, {ImGuiKey_Delete, "Delete"}, {ImGuiKey_Backspace, "Backspace"},
		{ImGuiKey_Space, "Space"}, {ImGuiKey_Enter, "Return"}, {ImGuiKey_Escape, "Escape"}, {ImGuiKey_LeftCtrl, "LeftCtrl", "Ctrl"},
		{ImGuiKey_LeftShift, "LeftShift", "Shift"}, {ImGuiKey_LeftAlt, "LeftAlt", "Alt"}, {ImGuiKey_LeftSuper, "LeftSuper", "Super"},
		{ImGuiKey_RightCtrl, "RightCtrl"}, {ImGuiKey_RightShift, "RightShift"}, {ImGuiKey_RightAlt, "RightAlt"},
		{ImGuiKey_RightSuper, "RightSuper"}, {ImGuiKey_Menu, "Menu"}, {ImGuiKey_0, "0"}, {ImGuiKey_1, "1"}, {ImGuiKey_2, "2"},
		{ImGuiKey_3, "3"}, {ImGuiKey_4, "4"}, {ImGuiKey_5, "5"}, {ImGuiKey_6, "6"}, {ImGuiKey_7, "7"}, {ImGuiKey_8, "8"}, {ImGuiKey_9, "9"},
		{ImGuiKey_A, "A"}, {ImGuiKey_B, "B"}, {ImGuiKey_C, "C"}, {ImGuiKey_D, "D"}, {ImGuiKey_E, "E"}, {ImGuiKey_F, "F"}, {ImGuiKey_G, "G"},
		{ImGuiKey_H, "H"}, {ImGuiKey_I, "I"}, {ImGuiKey_J, "J"}, {ImGuiKey_K, "K"}, {ImGuiKey_L, "L"}, {ImGuiKey_M, "M"}, {ImGuiKey_N, "N"},
		{ImGuiKey_O, "O"}, {ImGuiKey_P, "P"}, {ImGuiKey_Q, "Q"}, {ImGuiKey_R, "R"}, {ImGuiKey_S, "S"}, {ImGuiKey_T, "T"}, {ImGuiKey_U, "U"},
		{ImGuiKey_V, "V"}, {ImGuiKey_W, "W"}, {ImGuiKey_X, "X"}, {ImGuiKey_Y, "Y"}, {ImGuiKey_Z, "Z"}, {ImGuiKey_F1, "F1"},
		{ImGuiKey_F2, "F2"}, {ImGuiKey_F3, "F3"}, {ImGuiKey_F4, "F4"}, {ImGuiKey_F5, "F5"}, {ImGuiKey_F6, "F6"}, {ImGuiKey_F7, "F7"},
		{ImGuiKey_F8, "F8"}, {ImGuiKey_F9, "F9"}, {ImGuiKey_F10, "F10"}, {ImGuiKey_F11, "F11"}, {ImGuiKey_F12, "F12"},
		{ImGuiKey_Apostrophe, "Apostrophe"}, {ImGuiKey_Comma, "Comma"}, {ImGuiKey_Minus, "Minus"}, {ImGuiKey_Period, "Period"},
		{ImGuiKey_Slash, "Slash"}, {ImGuiKey_Semicolon, "Semicolon"}, {ImGuiKey_Equal, "Equal"}, {ImGuiKey_LeftBracket, "BracketLeft"},
		{ImGuiKey_Backslash, "Backslash"}, {ImGuiKey_RightBracket, "BracketRight"}, {ImGuiKey_GraveAccent, "QuoteLeft"},
		{ImGuiKey_CapsLock, "CapsLock"}, {ImGuiKey_ScrollLock, "ScrollLock"}, {ImGuiKey_NumLock, "NumLock"},
		{ImGuiKey_PrintScreen, "PrintScreen"}, {ImGuiKey_Pause, "Pause"}, {ImGuiKey_Keypad0, "Keypad0"}, {ImGuiKey_Keypad1, "Keypad1"},
		{ImGuiKey_Keypad2, "Keypad2"}, {ImGuiKey_Keypad3, "Keypad3"}, {ImGuiKey_Keypad4, "Keypad4"}, {ImGuiKey_Keypad5, "Keypad5"},
		{ImGuiKey_Keypad6, "Keypad6"}, {ImGuiKey_Keypad7, "Keypad7"}, {ImGuiKey_Keypad8, "Keypad8"}, {ImGuiKey_Keypad9, "Keypad9"},
		{ImGuiKey_KeypadDecimal, "KeypadPeriod"}, {ImGuiKey_KeypadDivide, "KeypadDivide"}, {ImGuiKey_KeypadMultiply, "KeypadMultiply"},
		{ImGuiKey_KeypadSubtract, "KeypadMinus"}, {ImGuiKey_KeypadAdd, "KeypadPlus"}, {ImGuiKey_KeypadEnter, "KeypadReturn"},
		{ImGuiKey_KeypadEqual, "KeypadEqual"}};

	s_imgui_key_map.clear();
	for (const KeyMapping& km : mapping)
	{
		std::optional<u32> map(InputManager::ConvertHostKeyboardStringToCode(km.name));
		if (!map.has_value() && km.alt_name)
			map = InputManager::ConvertHostKeyboardStringToCode(km.alt_name);
		if (map.has_value())
			s_imgui_key_map[map.value()] = km.index;
	}
}

bool ImGuiManager::LoadFontData()
{
	if (s_standard_font_data.empty())
	{
		pxAssertRel(!s_font_path.empty(), "Font path has not been set.");
		std::optional<std::vector<u8>> font_data = FileSystem::ReadBinaryFile(s_font_path.c_str());
		if (!font_data.has_value())
			return false;

		s_standard_font_data = std::move(font_data.value());
	}

	if (s_fixed_font_data.empty())
	{
		std::optional<std::vector<u8>> font_data = FileSystem::ReadBinaryFile(
			EmuFolders::GetOverridableResourcePath("fonts" FS_OSPATH_SEPARATOR_STR "RobotoMono-Medium.ttf").c_str());
		if (!font_data.has_value())
			return false;

		s_fixed_font_data = std::move(font_data.value());
	}

	if (s_emoji_font_data.empty())
	{
		std::optional<std::vector<u8>> font_data = FileSystem::ReadBinaryFile(
			EmuFolders::GetOverridableResourcePath("fonts" FS_OSPATH_SEPARATOR_STR "NotoColorEmoji-Regular.ttf").c_str());
		if (!font_data.has_value())
			return false;

		s_emoji_font_data = std::move(font_data.value());
	}

	if (s_icon_fa_font_data.empty())
	{
		std::optional<std::vector<u8>> font_data =
			FileSystem::ReadBinaryFile(EmuFolders::GetOverridableResourcePath("fonts" FS_OSPATH_SEPARATOR_STR "fa-solid-900.ttf").c_str());
		if (!font_data.has_value())
			return false;

		s_icon_fa_font_data = std::move(font_data.value());
	}

	if (s_icon_pf_font_data.empty())
	{
		std::optional<std::vector<u8>> font_data =
			FileSystem::ReadBinaryFile(EmuFolders::GetOverridableResourcePath("fonts" FS_OSPATH_SEPARATOR_STR "promptfont.otf").c_str());
		if (!font_data.has_value())
			return false;

		s_icon_pf_font_data = std::move(font_data.value());
	}

	return true;
}

void ImGuiManager::UnloadFontData()
{
	std::vector<u8>().swap(s_standard_font_data);
	std::vector<u8>().swap(s_fixed_font_data);
	std::vector<u8>().swap(s_emoji_font_data);
	std::vector<u8>().swap(s_icon_fa_font_data);
	std::vector<u8>().swap(s_icon_pf_font_data);
}

// A resonable default font size is recommended
#define FONT_BASE_SIZE 15.0f

ImFont* ImGuiManager::AddTextFont()
{
	// Exclude FA and PF ranges
	// clang-format off
	static constexpr ImWchar range_exclude_icons[] = { 0x2198,0x2199,0x219e,0x21a7,0x21b0,0x21b3,0x21ba,0x21c3,0x21ce,0x21d4,0x21dc,0x21dd,0x21e0,0x21e3,0x21e6,0x21e8,0x21f3,0x21f3,0x21f7,0x21fb,0x2206,0x2208,0x221a,0x221a,0x227a,0x227d,0x22bf,0x22c8,0x2349,0x2349,0x235a,0x2361,0x2364,0x2367,0x237a,0x237f,0x23b2,0x23b5,0x23cc,0x23cc,0x23f4,0x23f7,0x2427,0x243a,0x243d,0x243d,0x2443,0x2443,0x2460,0x246b,0x248f,0x248f,0x24f5,0x24ff,0x2605,0x2605,0x2699,0x2699,0x278a,0x278e,0xff21,0xff3a,0x0,0x0 };
	// clang-format on

	ImFontConfig cfg;
	cfg.FontDataOwnedByAtlas = false;
	cfg.GlyphExcludeRanges = range_exclude_icons;
	return ImGui::GetIO().Fonts->AddFontFromMemoryTTF(
		s_standard_font_data.data(), static_cast<int>(s_standard_font_data.size()), FONT_BASE_SIZE, &cfg, nullptr);
}

ImFont* ImGuiManager::AddFixedFont()
{
	ImFontConfig cfg;
	cfg.FontDataOwnedByAtlas = false;
	return ImGui::GetIO().Fonts->AddFontFromMemoryTTF(
		s_fixed_font_data.data(), static_cast<int>(s_fixed_font_data.size()), FONT_BASE_SIZE, &cfg, nullptr);
}

bool ImGuiManager::AddIconFonts()
{
	// Load FontAwesome after to avoid aliased codepoints overriding promptfont
	{
		// Exclude emojis
		static constexpr ImWchar range_exclude_emojis[] = {0x10000, 0x1ffff, 0x0, 0x0};

		ImFontConfig cfg;
		cfg.MergeMode = true;
		cfg.PixelSnapH = true;
		cfg.GlyphMinAdvanceX = FONT_BASE_SIZE;
		cfg.GlyphMaxAdvanceX = FONT_BASE_SIZE;
		cfg.GlyphExcludeRanges = range_exclude_emojis;
		cfg.FontDataOwnedByAtlas = false;

		if (!ImGui::GetIO().Fonts->AddFontFromMemoryTTF(
				s_icon_pf_font_data.data(), static_cast<int>(s_icon_pf_font_data.size()), FONT_BASE_SIZE * 1.2f, &cfg, nullptr))
		{
			return false;
		}
	}

	{
		// Exclude any characters outside the BMP PUA plane
		static constexpr ImWchar range_exclude_non_bmp[] = {0x1, 0xdfff, 0xf900, 0x10ffff, 0x0, 0x0};

		ImFontConfig cfg;
		cfg.MergeMode = true;
		cfg.PixelSnapH = true;
		cfg.GlyphMinAdvanceX = FONT_BASE_SIZE;
		cfg.GlyphMaxAdvanceX = FONT_BASE_SIZE;
		cfg.GlyphExcludeRanges = range_exclude_non_bmp;
		cfg.FontDataOwnedByAtlas = false;

		if (!ImGui::GetIO().Fonts->AddFontFromMemoryTTF(
				s_icon_fa_font_data.data(), static_cast<int>(s_icon_fa_font_data.size()), FONT_BASE_SIZE * 0.75f, &cfg, nullptr))
		{
			return false;
		}
	}

	return true;
}

bool ImGuiManager::AddEmojiFont()
{
	{
		// ImGui can't correctly handle some Unicode codepoints
		// Remove them to avoid rendering blank/fallback characters
		// See https://github.com/ocornut/imgui/issues/8240
		static ImFontLoader filter_loader;
		filter_loader.Name = "Emoji Preprocessor";
		filter_loader.FontSrcContainsGlyph = [](ImFontAtlas* atlas, ImFontConfig* src, ImWchar codepoint) {
			if (codepoint == 0xfe0e || codepoint == 0xfe0f)
				return true;
			return false;
		};
		filter_loader.FontBakedLoadGlyph = [](ImFontAtlas* atlas, ImFontConfig* src, ImFontBaked* baked, void*, ImWchar codepoint, ImFontGlyph* out_glyph, float* out_advance_x) {
			if (codepoint != 0xfe0e && codepoint != 0xfe0f)
				return false;

			// Metrics only mode
			if (out_advance_x != nullptr)
			{
				*out_advance_x = 0.0f;
				return true;
			}

			out_glyph->Codepoint = codepoint;
			out_glyph->AdvanceX = 0.0f;
			out_glyph->Visible = false;

			return true;
		};

		ImFontConfig cfg;
		StringUtil::Strlcpy(cfg.Name, filter_loader.Name, sizeof(cfg.Name));
		cfg.MergeMode = true;
		cfg.SizePixels = FONT_BASE_SIZE;
		cfg.FontLoader = &filter_loader;
		if (!ImGui::GetIO().Fonts->AddFont(&cfg))
			return false;
	}

	{
		ImFontConfig cfg;
		cfg.MergeMode = true;
		// Set GlyphMin/MaxAdvanceX to allow replacing FA/PF icons.
		cfg.GlyphMinAdvanceX = FONT_BASE_SIZE;
		cfg.GlyphMaxAdvanceX = FONT_BASE_SIZE;
		cfg.FontLoaderFlags |= ImGuiFreeTypeLoaderFlags_LoadColor;
		cfg.FontDataOwnedByAtlas = false;

		if (!ImGui::GetIO().Fonts->AddFontFromMemoryTTF(
				s_emoji_font_data.data(), static_cast<int>(s_emoji_font_data.size()), FONT_BASE_SIZE, &cfg, nullptr))
		{
			return false;
		}
	}
	return true;
}

bool ImGuiManager::AddImGuiFonts()
{
	ImGuiIO& io = ImGui::GetIO();
	io.Fonts->Clear();

	s_standard_font = AddTextFont();
	if (!s_standard_font || !AddIconFonts() || !AddEmojiFont())
		return false;

	s_fixed_font = AddFixedFont();
	if (!s_fixed_font || !AddEmojiFont())
		return false;

	ImGuiFullscreen::SetFont(s_standard_font);
	return true;
}

struct OSDMessage
{
	std::string key;
	std::string text;
	Common::Timer::Value start_time;
	Common::Timer::Value move_time;
	float duration;
	float target_y;
	float last_y;
};

static std::deque<OSDMessage> s_osd_active_messages;
static std::deque<OSDMessage> s_osd_posted_messages;
static std::mutex s_osd_messages_lock;

void Host::AddOSDMessage(std::string message, float duration /*= 2.0f*/)
{
	AddKeyedOSDMessage(std::string(), std::move(message), duration);
}

void Host::AddKeyedOSDMessage(std::string key, std::string message, float duration /* = 2.0f */)
{
	if (!key.empty())
		Console.WriteLn(Color_StrongGreen, fmt::format("OSD [{}]: {}", key, message));
	else
		Console.WriteLn(Color_StrongGreen, fmt::format("OSD: {}", message));

	const Common::Timer::Value current_time = Common::Timer::GetCurrentValue();

	OSDMessage msg;
	msg.key = std::move(key);
	msg.text = std::move(message);
	msg.start_time = current_time;
	msg.move_time = current_time;
	msg.duration = duration;
	msg.target_y = -1.0f;
	msg.last_y = -1.0f;

	std::unique_lock<std::mutex> lock(s_osd_messages_lock);
	s_osd_posted_messages.push_back(std::move(msg));
}

void Host::AddIconOSDMessage(std::string key, const char* icon, const std::string_view message, float duration /* = 2.0f */)
{
	if (!key.empty())
		Console.WriteLn(Color_StrongGreen, fmt::format("OSD [{}]: {}", key, message));
	else
		Console.WriteLn(Color_StrongGreen, fmt::format("OSD: {}", message));

	const Common::Timer::Value current_time = Common::Timer::GetCurrentValue();

	OSDMessage msg = {};
	msg.key = std::move(key);
	msg.text = fmt::format("{}  {}", icon, message);
	msg.start_time = current_time;
	msg.move_time = current_time;
	msg.duration = duration;
	msg.target_y = -1.0f;
	msg.last_y = -1.0f;

	std::unique_lock<std::mutex> lock(s_osd_messages_lock);
	s_osd_posted_messages.push_back(std::move(msg));
}

void Host::RemoveKeyedOSDMessage(std::string key)
{
	OSDMessage msg = {};
	msg.key = std::move(key);
	msg.duration = 0.0f;

	std::unique_lock<std::mutex> lock(s_osd_messages_lock);
	s_osd_posted_messages.push_back(std::move(msg));
}

void Host::ClearOSDMessages()
{
	{
		std::unique_lock<std::mutex> lock(s_osd_messages_lock);
		s_osd_posted_messages.clear();
	}

	s_osd_active_messages.clear();
}

void ImGuiManager::AcquirePendingOSDMessages(Common::Timer::Value current_time)
{
	std::atomic_thread_fence(std::memory_order_consume);
	if (s_osd_posted_messages.empty())
		return;
	std::unique_lock lock(s_osd_messages_lock);
	for (;;)
	{
		if (s_osd_posted_messages.empty())
			break;

		if (GSConfig.OsdMessagesPos != OsdOverlayPos::None)
		{
			OSDMessage& new_msg = s_osd_posted_messages.front();
			std::deque<OSDMessage>::iterator iter;
			if (!new_msg.key.empty() && (iter = std::find_if(s_osd_active_messages.begin(), s_osd_active_messages.end(),
											 [&new_msg](const OSDMessage& other) {
												 return new_msg.key == other.key;
											 })) != s_osd_active_messages.end())
			{
				iter->text = std::move(new_msg.text);
				iter->duration = new_msg.duration;

				// Don't fade it in again
				const float time_passed =
					static_cast<float>(Common::Timer::ConvertValueToSeconds(current_time - iter->start_time));
				iter->start_time =
					current_time - Common::Timer::ConvertSecondsToValue(std::min(time_passed, OSD_FADE_IN_TIME));
			}
			else
			{
				s_osd_active_messages.push_back(std::move(new_msg));
			}
		}
		s_osd_posted_messages.pop_front();

		static constexpr size_t MAX_ACTIVE_OSD_MESSAGES = 512;
		if (s_osd_active_messages.size() > MAX_ACTIVE_OSD_MESSAGES)
			s_osd_active_messages.pop_front();
	}
}

void ImGuiManager::DrawOSDMessages(Common::Timer::Value current_time)
{
	static constexpr float MOVE_DURATION = 0.5f;

	ImFont* const font = s_standard_font;
	const float font_size = GetFontSizeStandard();
	const float scale = s_global_scale;
	const float spacing = std::ceil(5.0f * scale);
	const float margin = std::ceil(10.0f * scale);
	const float padding = std::ceil(8.0f * scale);
	const float rounding = std::ceil(5.0f * scale);
	const float max_width = s_window_width - (margin + padding) * 2.0f;
	
	float position_y = margin;
	switch (GSConfig.OsdMessagesPos)
	{
		case OsdOverlayPos::TopLeft:
		case OsdOverlayPos::TopCenter:
		case OsdOverlayPos::TopRight:
			position_y = margin;
			break;
			
		case OsdOverlayPos::CenterLeft:
		case OsdOverlayPos::Center:
		case OsdOverlayPos::CenterRight:
			position_y = s_window_height * 0.5f;
			break;
			
		case OsdOverlayPos::BottomLeft:
		case OsdOverlayPos::BottomCenter:
		case OsdOverlayPos::BottomRight:
			// For bottom positions, start from the bottom and let messages stack upward
			position_y = s_window_height - margin;
			break;
			
		case OsdOverlayPos::None:
		default:
			position_y = margin;
			break;
	}

	auto iter = s_osd_active_messages.begin();
	while (iter != s_osd_active_messages.end())
	{
		OSDMessage& msg = *iter;
		const float time_passed = static_cast<float>(Common::Timer::ConvertValueToSeconds(current_time - msg.start_time));
		if (time_passed >= msg.duration)
		{
			iter = s_osd_active_messages.erase(iter);
			continue;
		}

		++iter;

		u8 opacity;
		if (time_passed < OSD_FADE_IN_TIME)
			opacity = static_cast<u8>((time_passed / OSD_FADE_IN_TIME) * 255.0f);
		else if (time_passed > (msg.duration - OSD_FADE_OUT_TIME))
			opacity = static_cast<u8>(std::min((msg.duration - time_passed) / OSD_FADE_OUT_TIME, 1.0f) * 255.0f);
		else
			opacity = 255;

		const float expected_y = position_y;
		float actual_y = msg.last_y;
		if (msg.target_y != expected_y)
		{
			if (msg.last_y < 0.0f)
			{
				// First showing.
				msg.last_y = expected_y;
			}
			else
			{
				// We got repositioned, probably due to another message above getting removed.
				const float time_since_move =
					static_cast<float>(Common::Timer::ConvertValueToSeconds(current_time - msg.move_time));
				const float frac = Easing::OutExpo(time_since_move / MOVE_DURATION);
				msg.last_y = std::floor(msg.last_y - ((msg.last_y - msg.target_y) * frac));
			}
			msg.move_time = current_time;
			msg.target_y = expected_y;
			actual_y = msg.last_y;
		}
		else if (actual_y != expected_y)
		{
			const float time_since_move =
				static_cast<float>(Common::Timer::ConvertValueToSeconds(current_time - msg.move_time));
			if (time_since_move >= MOVE_DURATION)
			{
				msg.move_time = current_time;
				msg.last_y = msg.target_y;
				actual_y = msg.last_y;
			}
			else
			{
				const float frac = Easing::OutExpo(time_since_move / MOVE_DURATION);
				actual_y = std::floor(msg.last_y - ((msg.last_y - msg.target_y) * frac));
			}
		}

		if (actual_y >= s_window_height)
			break;

		const ImVec2 text_size(
			font->CalcTextSizeA(font_size, max_width, max_width, msg.text.c_str(), msg.text.c_str() + msg.text.length()));
		const ImVec2 size(text_size.x + padding * 2.0f, text_size.y + padding * 2.0f);
		
		// For bottom positions, adjust actual_y to try to account for message height
		float final_y = actual_y;
		if (GSConfig.OsdMessagesPos == OsdOverlayPos::BottomLeft || 
		    GSConfig.OsdMessagesPos == OsdOverlayPos::BottomCenter || 
		    GSConfig.OsdMessagesPos == OsdOverlayPos::BottomRight)
		{
			final_y = actual_y - size.y;
		}
		
		const ImVec2 base_pos = CalculateOSDPosition(GSConfig.OsdMessagesPos, margin, size, s_window_width, s_window_height);
		const ImVec2 pos(base_pos.x, final_y);
		const ImVec4 text_rect(pos.x + padding, pos.y + padding, pos.x + size.x - padding, pos.y + size.y - padding);

		ImDrawList* dl = ImGui::GetBackgroundDrawList();
		dl->AddRectFilled(pos, ImVec2(pos.x + size.x, pos.y + size.y), IM_COL32(0x21, 0x21, 0x21, opacity), rounding);
		dl->AddRect(pos, ImVec2(pos.x + size.x, pos.y + size.y), IM_COL32(0x48, 0x48, 0x48, opacity), rounding);
		dl->AddText(font, font_size, ImVec2(text_rect.x, text_rect.y), IM_COL32(0xff, 0xff, 0xff, opacity), msg.text.c_str(),
			msg.text.c_str() + msg.text.length(), max_width, &text_rect);
		
		// Stack direction depends on the position upward for bottom positions, downward for others
		if (GSConfig.OsdMessagesPos == OsdOverlayPos::BottomLeft || 
		    GSConfig.OsdMessagesPos == OsdOverlayPos::BottomCenter || 
		    GSConfig.OsdMessagesPos == OsdOverlayPos::BottomRight)
		{
			position_y -= (size.y + spacing); // Stack upward for bottom positions
		}
		else
		{
			position_y += size.y + spacing; // Stack downward for top/center positions
		}
	}
}

void ImGuiManager::RenderOSD()
{
	// acquire for IO.MousePos.
	std::atomic_thread_fence(std::memory_order_acquire);

	// Don't draw OSD when we're just running big picture.
	if (VMManager::HasValidVM())
		RenderOverlays();

	const Common::Timer::Value current_time = Common::Timer::GetCurrentValue();
	AcquirePendingOSDMessages(current_time);
	DrawOSDMessages(current_time);

	// Cursors are always last.
	DrawSoftwareCursors();
}

float ImGuiManager::GetGlobalScale()
{
	return s_global_scale;
}

ImFont* ImGuiManager::GetStandardFont()
{
	return s_standard_font;
}

ImFont* ImGuiManager::GetFixedFont()
{
	return s_fixed_font;
}

float ImGuiManager::GetFontSizeStandard()
{
	return std::ceil(15.0f * s_global_scale);
}

float ImGuiManager::GetFontSizeMedium()
{
	return ImGuiFullscreen::LayoutScale(ImGuiFullscreen::LAYOUT_MEDIUM_FONT_SIZE);
}

float ImGuiManager::GetFontSizeLarge()
{
	return ImGuiFullscreen::LayoutScale(ImGuiFullscreen::LAYOUT_LARGE_FONT_SIZE);
}

bool ImGuiManager::WantsTextInput()
{
	return s_imgui_wants_text.load(std::memory_order_acquire);
}

bool ImGuiManager::WantsMouseInput()
{
	return s_imgui_wants_mouse.load(std::memory_order_acquire);
}

void ImGuiManager::AddTextInput(std::string str)
{
	if (!s_imgui_wants_text.load(std::memory_order_acquire))
		return;

	// Has to go through the CPU -> GS thread :(
	Host::RunOnCPUThread([str = std::move(str)]() {
		MTGS::RunOnGSThread([str = std::move(str)]() {
			if (!ImGui::GetCurrentContext())
				return;

			ImGui::GetIO().AddInputCharactersUTF8(str.c_str());
		});
	});
}

void ImGuiManager::UpdateMousePosition(float x, float y)
{
	if (!ImGui::GetCurrentContext())
		return;

	ImGui::GetIO().MousePos = ImVec2(x, y);
	std::atomic_thread_fence(std::memory_order_release);
}

bool ImGuiManager::ProcessPointerButtonEvent(InputBindingKey key, float value)
{
	if (!ImGui::GetCurrentContext() || key.data >= std::size(ImGui::GetIO().MouseDown))
		return false;

	// still update state anyway
	MTGS::RunOnGSThread([button = key.data, down = (value != 0.0f)]() { ImGui::GetIO().AddMouseButtonEvent(button, down); });

	return s_imgui_wants_mouse.load(std::memory_order_acquire);
}

bool ImGuiManager::ProcessPointerAxisEvent(InputBindingKey key, float value)
{
	if (!ImGui::GetCurrentContext() || value == 0.0f || key.data < static_cast<u32>(InputPointerAxis::WheelX))
		return false;

	// still update state anyway
	const bool horizontal = (key.data == static_cast<u32>(InputPointerAxis::WheelX));
	MTGS::RunOnGSThread([wheel_x = horizontal ? value : 0.0f, wheel_y = horizontal ? 0.0f : value]() {
		ImGui::GetIO().AddMouseWheelEvent(wheel_x, wheel_y);
	});

	return s_imgui_wants_mouse.load(std::memory_order_acquire);
}

bool ImGuiManager::ProcessHostKeyEvent(InputBindingKey key, float value)
{
	decltype(s_imgui_key_map)::iterator iter;
	if (!ImGui::GetCurrentContext() || (iter = s_imgui_key_map.find(key.data)) == s_imgui_key_map.end())
		return false;

	// still update state anyway
	MTGS::RunOnGSThread([imkey = iter->second, down = (value != 0.0f)]() { ImGui::GetIO().AddKeyEvent(imkey, down); });

	return s_imgui_wants_keyboard.load(std::memory_order_acquire);
}

bool ImGuiManager::ProcessGenericInputEvent(GenericInputBinding key, InputLayout layout, float value)
{
	static constexpr ImGuiKey key_map[] = {
		ImGuiKey_None, // Unknown,
		ImGuiKey_GamepadDpadUp, // DPadUp
		ImGuiKey_GamepadDpadRight, // DPadRight
		ImGuiKey_GamepadDpadLeft, // DPadLeft
		ImGuiKey_GamepadDpadDown, // DPadDown
		ImGuiKey_None, // LeftStickUp
		ImGuiKey_None, // LeftStickRight
		ImGuiKey_None, // LeftStickDown
		ImGuiKey_None, // LeftStickLeft
		ImGuiKey_GamepadL3, // L3
		ImGuiKey_None, // RightStickUp
		ImGuiKey_None, // RightStickRight
		ImGuiKey_None, // RightStickDown
		ImGuiKey_None, // RightStickLeft
		ImGuiKey_GamepadR3, // R3
		ImGuiKey_GamepadFaceUp, // Triangle
		ImGuiKey_GamepadFaceRight, // Circle
		ImGuiKey_GamepadFaceDown, // Cross
		ImGuiKey_GamepadFaceLeft, // Square
		ImGuiKey_GamepadBack, // Select
		ImGuiKey_GamepadStart, // Start
		ImGuiKey_None, // System
		ImGuiKey_GamepadL1, // L1
		ImGuiKey_GamepadL2, // L2
		ImGuiKey_GamepadR1, // R1
		ImGuiKey_GamepadL2, // R2
	};

	if (!ImGui::GetCurrentContext())
		return false;

	if (static_cast<u32>(key) >= std::size(key_map) || key_map[static_cast<u32>(key)] == ImGuiKey_None)
		return false;

	MTGS::RunOnGSThread(
		[key = key_map[static_cast<u32>(key)], value, layout]() mutable {
			if (s_gamepad_swap_noth_west)
			{
				if (key == ImGuiKey_GamepadFaceUp)
					key = ImGuiKey_GamepadFaceLeft;
				else if (key == ImGuiKey_GamepadFaceLeft)
					key = ImGuiKey_GamepadFaceUp;
			}

			ImGuiFullscreen::ReportGamepadLayout(layout);
			ImGui::GetIO().AddKeyAnalogEvent(key, (value > 0.0f), value);
		});

	return s_imgui_wants_keyboard.load(std::memory_order_acquire);
}

void ImGuiManager::SwapGamepadNorthWest(bool value)
{
	s_gamepad_swap_noth_west = value;
}

bool ImGuiManager::IsGamepadNorthWestSwapped()
{
	return s_gamepad_swap_noth_west;
}

void ImGuiManager::CreateSoftwareCursorTextures()
{
	for (u32 i = 0; i < InputManager::MAX_POINTER_DEVICES; i++)
	{
		if (!s_software_cursors[i].image_path.empty())
			UpdateSoftwareCursorTexture(i);
	}
}

void ImGuiManager::DestroySoftwareCursorTextures()
{
	for (u32 i = 0; i < InputManager::MAX_POINTER_DEVICES; i++)
	{
		s_software_cursors[i].texture.reset();
	}
}

void ImGuiManager::UpdateSoftwareCursorTexture(u32 index)
{
	SoftwareCursor& sc = s_software_cursors[index];
	if (sc.image_path.empty())
	{
		sc.texture.reset();
		return;
	}

	RGBA8Image image;
	if (!image.LoadFromFile(sc.image_path.c_str()))
	{
		Console.Error("Failed to load software cursor %u image '%s'", index, sc.image_path.c_str());
		return;
	}
	sc.texture = std::unique_ptr<GSTexture>(g_gs_device->CreateTexture(image.GetWidth(), image.GetHeight(), 1, GSTexture::Format::Color));
	if (!sc.texture)
	{
		Console.Error(
			"Failed to upload %ux%u software cursor %u image '%s'", image.GetWidth(), image.GetHeight(), index, sc.image_path.c_str());
		return;
	}
	sc.texture->Update(GSVector4i(0, 0, image.GetWidth(), image.GetHeight()), image.GetPixels(), image.GetPitch(), 0);

	sc.extent_x = std::ceil(static_cast<float>(image.GetWidth()) * sc.scale * s_global_scale) / 2.0f;
	sc.extent_y = std::ceil(static_cast<float>(image.GetHeight()) * sc.scale * s_global_scale) / 2.0f;
}

void ImGuiManager::DrawSoftwareCursor(const SoftwareCursor& sc, const std::pair<float, float>& pos)
{
	if (!sc.texture)
		return;

	const ImVec2 min(pos.first - sc.extent_x, pos.second - sc.extent_y);
	const ImVec2 max(pos.first + sc.extent_x, pos.second + sc.extent_y);

	ImDrawList* dl = ImGui::GetForegroundDrawList();

	dl->AddImage(
		reinterpret_cast<ImTextureID>(sc.texture.get()->GetNativeHandle()), min, max, ImVec2(0.0f, 0.0f), ImVec2(1.0f, 1.0f), sc.color);
}

void ImGuiManager::DrawSoftwareCursors()
{
	// This one's okay to race, worst that happens is we render the wrong number of cursors for a frame.
	const u32 pointer_count = InputManager::MAX_POINTER_DEVICES;
	for (u32 i = 0; i < pointer_count; i++)
		DrawSoftwareCursor(s_software_cursors[i], InputManager::GetPointerAbsolutePosition(i));

	for (u32 i = InputManager::MAX_POINTER_DEVICES; i < InputManager::MAX_SOFTWARE_CURSORS; i++)
		DrawSoftwareCursor(s_software_cursors[i], s_software_cursors[i].pos);
}

void ImGuiManager::SetSoftwareCursor(u32 index, std::string image_path, float image_scale, u32 multiply_color)
{
	MTGS::RunOnGSThread([index, image_path = std::move(image_path), image_scale, multiply_color]() {
		pxAssert(index < std::size(s_software_cursors));
		SoftwareCursor& sc = s_software_cursors[index];
		sc.color = multiply_color | 0xFF000000;
		if (sc.image_path == image_path && sc.scale == image_scale)
			return;

		const bool is_hiding_or_showing = (image_path.empty() != sc.image_path.empty());
		sc.image_path = std::move(image_path);
		sc.scale = image_scale;
		if (MTGS::IsOpen())
			UpdateSoftwareCursorTexture(index);

		// Hide the system cursor when we activate a software cursor.
		if (is_hiding_or_showing && index == 0)
			Host::RunOnCPUThread(&InputManager::UpdateHostMouseMode);
	});
}

bool ImGuiManager::HasSoftwareCursor(u32 index)
{
	return (index < s_software_cursors.size() && !s_software_cursors[index].image_path.empty());
}

void ImGuiManager::ClearSoftwareCursor(u32 index)
{
	SetSoftwareCursor(index, std::string(), 0.0f, 0);
}

void ImGuiManager::SetSoftwareCursorPosition(u32 index, float pos_x, float pos_y)
{
	pxAssert(index < InputManager::MAX_SOFTWARE_CURSORS);
	SoftwareCursor& sc = s_software_cursors[index];
	sc.pos.first = pos_x;
	sc.pos.second = pos_y;
}

std::string ImGuiManager::StripIconCharacters(std::string_view str)
{
	std::string result;
	result.reserve(str.length());

	for (size_t offset = 0; offset < str.length();)
	{
		char32_t utf;
		offset += StringUtil::DecodeUTF8(str, offset, &utf);

		// icon if outside BMP/SMP/TIP, or inside private use area
		if (utf > 0x32FFF || (utf >= 0xE000 && utf <= 0xF8FF))
			continue;

		StringUtil::EncodeAndAppendUTF8(result, utf);
	}

	StringUtil::StripWhitespace(&result);

	return result;
}
