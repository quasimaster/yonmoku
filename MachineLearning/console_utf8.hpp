#pragma once

#include <cstdlib>

// Windows のコンソールは既定で CP932(Shift_JIS)のため、UTF-8 で保存された
// ソース中の日本語をそのまま cout / cerr へ流すと文字化けする。
// main() の先頭で enable_utf8_console() を呼び、コンソール側の出力コードページを
// UTF-8(65001)へ合わせることで解決する。
//
//   ・<windows.h> は include しない。min/max マクロなどが common.hpp の
//     std::min / std::max と衝突するため、必要な 2 関数だけを自前で宣言する。
//   ・リダイレクト時(> log.txt)はコンソールを経由しないので、この設定に関係なく
//     UTF-8 のバイト列がそのまま書き出される。もともと化けない。
//   ・コードページはコンソール全体の設定でプロセス終了後も残るため、
//     atexit で元に戻す(他の Shift_JIS 前提のプログラムを巻き込まないように)。

#ifdef _WIN32
extern "C" __declspec(dllimport) int          __stdcall SetConsoleOutputCP(unsigned int wCodePageID);
extern "C" __declspec(dllimport) unsigned int __stdcall GetConsoleOutputCP(void);
#endif

inline void enable_utf8_console()
{
#ifdef _WIN32
	static bool done = false;
	if (done) return;
	done = true;

	const unsigned int prev = GetConsoleOutputCP();
	if (prev == 0 || prev == 65001) return;   // コンソールが無い / 既に UTF-8 なら何もしない
	if (!SetConsoleOutputCP(65001)) return;   // 切り替えられなければ黙って諦める

	static unsigned int saved = prev;
	atexit([]{ SetConsoleOutputCP(saved); });
#endif
}
