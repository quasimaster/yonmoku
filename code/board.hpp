// =============================================================================
//  board.hpp(コメント付き)
//  解説: c109-gijutsushoten/explanation/ の解説 tex
//
//  立体四目並べの盤面 Board と、勝ちライン表 LINES を作る init_lines()。
//
//  ■ ビットボード
//    盤面は 64マスなので、「石があるマスのビットを 1 にした 64 bit 整数」で 1色分を表せる。
//    Board はこれを 2つ持つ。
//      Me  … これから石を置く側(手番側)の石
//      You … 相手の石
//    石を置くたびに Me と You を入れ替える(swap)ので、常に「Me = 手番側」が成り立つ。
//    白/黒のどちらが手番かは、石の総数の偶奇から分かる(player() / validate())。
//
//  ■ シフト演算の読み方
//    マス番号は x + 4y + 16z(common.hpp)なので、ビットを
//      1つずらす  … x 方向に 1マス
//      4つずらす  … y 方向に 1マス
//      16 ずらす   … z 方向(高さ)に 1マス
//    移動することになる。B >> k は「各マスに、k 先のマスの値を持ってくる」演算と読める。
//    つまり (B & B >> k) の bit i が 1 ⇔ マス i と マス i+k の両方に石がある。
//
//  ★元のコードからの変更は、先手を白・後手を黒とする色の名前の入れ替え(enum Color など)と、コメントの追加だけである。
// =============================================================================

#pragma once

#include "common.hpp"

//static const int sparse = 1;
struct Board
{
	// Me = 手番側の石、You = 相手の石(どちらも 64 bit のビットボード)。
	unsigned long long Me, You;

	// 空の盤面で初期化する。
	Board() : Me(0uLL), You(0uLL) {}

	// -------------------------------------------------------------------------
	//  win(B): ビットボード B の中に 4つ並びが 1つでもあれば End、無ければ Continue。
	//
	//  方針: 方向ごとに「間隔 d で 4つ並んでいるか」をシフト 2回で調べる。
	//    b = B & B >> 2d   … マス i と i+2d の両方に石
	//    b & b >> d        … さらに i+d と i+3d にも石 → i, i+d, i+2d, i+3d の 4つ並び
	//  ただし x や y 方向にずらすと、行の端から次の行へ「はみ出して」つながって見えてしまう。
	//  そこで並びの始点 i になれるマス(例: x 方向なら x = 0 のマス)だけを mask で残す。
	//  static: 盤面に依存しない関数なので、Board::win(ビット列) と呼べる。
	// -------------------------------------------------------------------------
	static inline enum State win(const unsigned long long B)
	{
		{//z dir
			// 縦方向(間隔 16)。i, i+16, i+32, i+48 がすべて 64 未満になるのは z = 0 のマスだけで、
			// それ以外は右シフトでビットが消えるので、はみ出しが起きず mask は要らない。
			unsigned long long b = B & B >> 2 * SIZE * SIZE;
			//static const unsigned long long mask = 0x000000000000ffffuLL;
			if (b & b >> SIZE * SIZE) return State::End;
		}
		{//x dir
			// x 方向(間隔 1)。始点は x = 0 のマスだけ。
			// 0x1111... = 各 4 bit の最下位 = x = 0 のマス 16個。
			unsigned long long b = B & B >> 2;
			static const unsigned long long mask = 0x1111111111111111uLL;
			if (b & b >> 1 & mask) return State::End;
		}
		{//y dir
			// y 方向(間隔 4)。始点は y = 0 のマスだけ。
			// 0x000f000f000f000f = 各段の下位 4 bit = 各段の y = 0 の行。
			unsigned long long b = B & B >> 2 * SIZE;
			static const unsigned long long mask = 0x000f000f000f000fuLL;
			if (b & b >> SIZE & mask) return State::End;
		}
		{//yz dir
			// yz 平面の斜め(x を固定し、y と z が同時に変わる)。
			{
				// y も z も増える向き(間隔 4 + 16 = 20)。始点 (x, 0, 0) から +60 で 63 以下に収まる
				// 始点は bit 0〜3 だけなので、mask は不要。
				unsigned long long b = B & B >> 2 * (SIZE * SIZE + SIZE);
				//static const unsigned long long mask = 0x000000000000000fuLL;
				if (b & b >> SIZE * SIZE + SIZE) return State::End;
			}
			{
				// y が減り z が増える向き(間隔 16 - 4 = 12)。始点は (x, 3, 0) = bit 12〜15。
				unsigned long long b = B & B >> 2 * (SIZE * SIZE - SIZE);
				static const unsigned long long mask = 0x000000000000f000uLL;
				if (b & b >> SIZE * SIZE - SIZE & mask) return State::End;
			}
		}
		{//zx dir
			// zx 平面の斜め(y を固定し、z と x が同時に変わる)。
			{
				// x も z も増える向き(間隔 17)。始点は (0, y, 0) = bit 0, 4, 8, 12。
				unsigned long long b = B & B >> 2 * (SIZE * SIZE + 1);
				static const unsigned long long mask = 0x0000000000001111uLL;
				if (b & b >> SIZE * SIZE + 1 & mask) return State::End;
			}
			{
				// x が減り z が増える向き(間隔 15)。始点は (3, y, 0) = bit 3, 7, 11, 15。
				unsigned long long b = B & B >> 2 * (SIZE * SIZE - 1);
				static const unsigned long long mask = 0x0000000000008888uLL;
				if (b & b >> SIZE * SIZE - 1 & mask) return State::End;
			}
		}
		{//xy dir
			// xy 平面の斜め(z を固定した水平面内の対角線)。
			{
				// x も y も増える向き(間隔 5)。始点は各段の (0, 0) = 各 16 bit の bit 0。
				unsigned long long b = B & B >> 2 * (SIZE + 1);
				static const unsigned long long mask = 0x0001000100010001uLL;
				if (b & b >> SIZE + 1 & mask) return State::End;
			}
			{
				// x が減り y が増える向き(間隔 3)。始点は各段の (3, 0) = 各 16 bit の bit 3。
				unsigned long long b = B & B >> 2 * (SIZE - 1);
				static const unsigned long long mask = 0x0008000800080008uLL;
				if (b & b >> SIZE - 1 & mask) return State::End;
			}
		}
		{//xyz dir
			// 立体の対角線(x, y, z がすべて変わる)は 4本しかないので、
			// 4マスのビット集合を直接作り、全部そろっているかを比べる。
			{
				// (0,0,0) → (3,3,3)
				static const unsigned long long line = BIT(0, 0, 0) | BIT(1, 1, 1) | BIT(2, 2, 2) | BIT(3, 3, 3);
				if ((B & line) == line) return State::End;
			}
			{
				// (0,0,3) → (3,3,0)
				static const unsigned long long line = BIT(0, 0, 3) | BIT(1, 1, 2) | BIT(2, 2, 1) | BIT(3, 3, 0);
				if ((B & line) == line) return State::End;
			}
			{
				// (0,3,0) → (3,0,3)
				static const unsigned long long line = BIT(0, 3, 0) | BIT(1, 2, 1) | BIT(2, 1, 2) | BIT(3, 0, 3);
				if ((B & line) == line) return State::End;
			}
			{
				// (0,3,3) → (3,0,0)
				static const unsigned long long line = BIT(0, 3, 3) | BIT(1, 2, 2) | BIT(2, 1, 1) | BIT(3, 0, 0);
				if ((B & line) == line) return State::End;
			}
		}
		// どの方向にも 4つ並びが無かった。
		return State::Continue;
	}

	// -------------------------------------------------------------------------
	//  reach(B): 「そこに B の石を置けば 4つ並ぶ」マス(決勝点)をすべて返す。
	//
	//  あるライン上で B の石が 3つあり、残り 1マスが B の石でないとき、その残り 1マスを返す。
	//  ★返すマスが空きかどうかは確かめていない(相手の石がある場合も含む)。
	//    また重力のため、すぐに置けるとも限らない(直下が空いている浮き決勝点も含む)。
	//    そのため呼び出し側は「hand & reach(...)」のように、合法手の集合との AND を取って使う。
	//
	//  縦・x・y 方向はシフト演算で、斜め 28本は LINES 表を使ったループで求める。
	// -------------------------------------------------------------------------
	static inline unsigned long long reach(const unsigned long long B)
	{
		unsigned long long ret = 0uLL;
		{//z dir
			// b の bit i が 1 ⇔ マス i と i+16(真上)の両方に石。
			// 縦 4マスのうち抜けている 1マスの位置(4通り)ごとに、残り 3マスの条件を組み立てる。
			const unsigned long long b = B & B >> SIZE * SIZE;
			// 4段目が抜け: 1・2・3段目に石(B<<16 で 1つ下、b<<48 で 3つ下と 2つ下)
			ret |= B << SIZE * SIZE & b << 3 * SIZE * SIZE;
			// 3段目が抜け: 1・2段目と 4段目に石
			ret |= B >> SIZE * SIZE & b << 2 * SIZE * SIZE;
			// 2段目が抜け: 1段目と 3・4段目に石
			ret |= b >> SIZE * SIZE & B << SIZE * SIZE;
			// 1段目が抜け: 2・3・4段目に石
			ret |= b >> 2 * SIZE * SIZE & B >> SIZE * SIZE;
		}
		{//x dir
			// b の bit i が 1 ⇔ マス i と i+1(x 方向の隣)の両方に石。
			// 抜けているマスの x 座標(0〜3)ごとに、そのマスだけを mask で残す(行のはみ出し防止)。
			const unsigned long long b = B & B >> 1;
			{
				// x = 0 が抜け: x = 1, 2, 3 に石
				static const unsigned long long mask = 0x1111111111111111uLL;
				ret |= mask & B >> 1 & b >> 2;
			}
			{
				// x = 1 が抜け: x = 0 と x = 2, 3 に石
				static const unsigned long long mask = 0x2222222222222222uLL;
				ret |= mask & B << 1 & b >> 1;
			}
			{
				// x = 2 が抜け: x = 0, 1 と x = 3 に石
				static const unsigned long long mask = 0x4444444444444444uLL;
				ret |= mask & b << 2 & B >> 1;
			}
			{
				// x = 3 が抜け: x = 0, 1, 2 に石
				static const unsigned long long mask = 0x8888888888888888uLL;
				ret |= mask & b << 3 & B << 1;
			}
		}
		{//y dir
			// x 方向と同じ考え方で、間隔を 4(y 方向に 1マス)にしたもの。
			// mask は各段の y = 0, 1, 2, 3 の行(4 bit ずつ)。
			const unsigned long long b = B & B >> SIZE;
			{
				// y = 0 が抜け
				static const unsigned long long mask = 0x000f000f000f000fuLL;
				ret |= mask & B >> SIZE & b >> 2 * SIZE;
			}
			{
				// y = 1 が抜け
				static const unsigned long long mask = 0x00f000f000f000f0uLL;
				ret |= mask & B << SIZE & b >> SIZE;
			}
			{
				// y = 2 が抜け
				static const unsigned long long mask = 0x0f000f000f000f00uLL;
				ret |= mask & b << 2 * SIZE & B >> SIZE;
			}
			{
				// y = 3 が抜け
				static const unsigned long long mask = 0xf000f000f000f000uLL;
				ret |= mask & b << 3 * SIZE & B << SIZE;
			}
		}
		// 斜めのライン(LINES[48]〜LINES[75] の 28本)は表で調べる。
		// SIZE * SIZE * 3 = 48 は「縦・x・y 方向の 16本 × 3」の後ろ、つまり斜めの先頭の添字。
		for (int i = SIZE * SIZE * 3; i < LINES_NUM; i++)
		{
			// ライン上で B の石が無いマスの集合。
			const unsigned long long b = LINES[i] & ~B;
			// b & -b は b の最下位ビットだけを取り出す。それが b 自身と等しい
			// ⇔ b のビットが 1個(= 石が 3つ並び、残りが 1マス)。そのマスを決勝点に加える。
			// (b = 0 のときも成り立つが、ret |= 0 なので影響はない)
			if ((b & -b) == b) ret |= b;
		}
		return ret;
	}

	// (x, y, z) のマスの状態を返す(手番側の石 / 相手の石 / 空き)。
	inline enum Cell get_cell(int x, int y, int z) const
	{
		unsigned long long bit = BIT(x, y, z);
		if (Me & bit)return Cell::Me;
		else if (You & bit) return Cell::You;
		else return Cell::None;
	}

	// 手数(何手目か)= 盤上の石の数 + 1。初期局面は 1手目、最後の 64マス目を置くのが 64手目。
	// __builtin_popcountll は 1 になっているビットの数を数える GCC の組み込み関数。
	int turn() const
	{
		return __builtin_popcountll(Me | You) + 1;
	}

	// 盤面の整合性を確かめ、手番の色を返す(デバッグ用。assert は NDEBUG で無効になる)。
	//   - 同じマスに両方の石が無いこと
	//   - 白番なら Me(白)と You(黒)が同数、黒番なら Me(黒)が 1個少ないこと
	enum Color validate() const
	{
		assert(!(Me & You));
		const int d = __builtin_popcountll(Me) - __builtin_popcountll(You);
		assert(d == 0 || d == -1);
		return d == 0 ? Color::White : Color::Black;
	}

	// 手番の色を返す(高速版)。石の総数が偶数なら白番、奇数なら黒番。
	// __builtin_parityll は 1 のビット数が奇数なら 1 を返す。
	enum Color player() const
	{
		return __builtin_parityll(Me | You) ? Color::Black : Color::White;
	}

	// 盤面をコンソールに表示する。4つの段を横に並べ、上の行ほど y が大きい。
	// 白は赤い X(\033[31m ... \033[m は端末の文字色を赤にするエスケープシーケンス)、黒は O、空きは -。
	void print() const
	{
		// Me / You を白 / 黒に読み替える。
		enum Color now = validate();
		unsigned long long white, black;
		if (now == Color::White) white = Me, black = You;
		else white = You, black = Me;
		// 表示上の座標は 1 始まり(内部は 0 始まり)。
		cout << "    z=1  z=2  z=3  z=4\n";
		for (int y = SIZE - 1; y >= 0; y--)
		{
			cout << "y=" << y + 1 << " ";
			for (int z = 0; z < SIZE; z++)
			{
				for (int x = 0; x < SIZE; x++)
				{
					const unsigned long long bit = BIT(x, y, z);
					{
						if (white & bit) cout << "\033[31mX\033[m";
						else if (black & bit) cout << "O";
						else cout << "-";
					}
				}
				if (z + 1 < SIZE) cout << " ";
			}
			cout << "\n";
		}
		cout << "  x=1234 1234 1234 1234" << endl;
	}

	// 76本の勝ちラインそれぞれについて、石の数を符号付きで返す(評価関数の特徴量)。
	//   両者の石が混在 → 0(どちらももう 4つ並べられない「死んだ」ライン)
	//   手番側の石だけ → +(石の数)  1〜3
	//   相手の石だけ   → -(石の数) -1〜-3
	//   石が無い       → 0(else 側で -0 になる)
	// ※探索内部では、これを毎回数え直さずに済むよう board_inc.hpp の BoardInc を使う。
	array<int, LINES_NUM> count() const
	{
		array<int, LINES_NUM> ret;
		for (int i = 0; i < LINES_NUM; i++)
		{
			if ((Me & LINES[i]) && (You & LINES[i])) ret[i] = 0;
			else if (Me & LINES[i]) ret[i] = __builtin_popcountll(Me & LINES[i]);
			else ret[i] = - __builtin_popcountll(You & LINES[i]);
		}
		return ret;
	}


	// -------------------------------------------------------------------------
	//  place(x, y): 柱 (x, y) に手番側の石を落とす(人間の入力など、座標で着手する場合)。
	//  重力があるので、置かれる高さ z はその柱で一番下の空きマスになる。
	//  戻り値: 範囲外・満杯なら Invalid、着手で 4つ並べば End、それ以外は Continue。
	// -------------------------------------------------------------------------
	enum State place(int x, int y)
	{
		// 盤の外の柱は置けない(表示は 1 始まりに直す)。
		if (x < 0 || 4 <= x || y < 0 || 4 <= y)
		{
			cout << "out of range : (" << x + 1 << ", " << y + 1 << ")" << endl;
			return State::Invalid;
		}
		// 下から順に見て、最初の空きマスの高さを探す。
		int z = 0;
		while (z < 4 && get_cell(x, y, z) != Cell::None) z++;
		// 4段すべて埋まっていれば置けない。
		if (z == 4)
		{
			cout << "row (" << x + 1 << ", " << y + 1 << ") is full" << endl;
			return State::Invalid;
		}
		// 手番側に石を加え、手番を交代する(Me と You を入れ替える)。
		Me |= BIT(x, y, z);
		swap(Me, You);
		// 入れ替え後は You が「今置いた側」なので、You に 4つ並びができたかを調べる。
		return win(You);
	}

	// place の高速版(探索用)。置くマスのビット bit を直接受け取り、範囲や重力の確認はしない。
	// bit は valid_move() が返した合法手のどれか 1つであることが前提。
	enum State place_fast(unsigned long long bit)
	{
		Me |= bit;
		swap(Me, You);
		return win(You);
	}

	// -------------------------------------------------------------------------
	//  valid_move(): 今置ける全マス(合法手)のビット集合を返す。
	//  重力があるので、置けるのは「1段目の空きマス」か「石があるマスの真上の空きマス」。
	//    (Me | You) << 16  … 石があるマスの 1段上のマス
	//    (1 << 16) - 1     … 1段目の全マス(0xFFFF)
	//    & ~(Me | You)     … そのうち空いているマス
	//  柱ごとに高々 1マスなので、合法手は最大 16個。
	// -------------------------------------------------------------------------
	unsigned long long valid_move() const
	{
		return ((Me | You) << SIZE * SIZE | ((1uLL << SIZE * SIZE) - 1)) & ~(Me | You);
	}

	// place_fast の「元の盤面を変えない」版。石を置いて手番を替えた新しい盤面を返す。
	// 勝敗判定はしない(探索側で別に行う)。探索で子局面を作るときに使う。
	Board place_fast_clone(unsigned long long bit) const
	{
		Board b = *this;
		b.Me |= bit;
		swap(b.Me, b.You);
		return b;
	}
};

// =============================================================================
//  init_lines(): 勝ちライン表 LINES[76] を作り、正しいかを確かめる。
//  LINES は reach() や評価関数が使うので、プログラムの最初(main() の先頭)で一度だけ呼ぶこと。
//  ライン 1本は「4マスのビットを OR した 64 bit 値」。方向ごとに順に作って lines に積む。
// =============================================================================
// LINES の構築・検証と move_order の全網羅検証。main() の先頭で一度呼ぶこと。
inline void init_lines()
{
	{
		vector<unsigned long long> lines;
		// lines.reserve(LINES_NUM);

		// [0..15] 縦(z 方向): 柱 (x, y) ごとに z = 0〜3 の 4マス。添字 = 4x + y。
		for (int x = 0; x < SIZE; x++) for (int y = 0; y < SIZE; y++)
		{
			unsigned long long line = 0uLL;
			for (int z = 0; z < SIZE; z++) line |= BIT(x, y, z);
			lines.push_back(line);

		}
		// [16..31] x 方向: (y, z) ごとに x = 0〜3 の 4マス。
		for (int y = 0; y < SIZE; y++) for (int z = 0; z < SIZE; z++)
		{
			unsigned long long line = 0uLL;
			for (int x = 0; x < SIZE; x++) line |= BIT(x, y, z);
			lines.push_back(line);

		}
		// [32..47] y 方向: (z, x) ごとに y = 0〜3 の 4マス。
		for (int z = 0; z < SIZE; z++) for (int x = 0; x < SIZE; x++)
		{
			unsigned long long line = 0uLL;
			for (int y = 0; y < SIZE; y++) line |= BIT(x, y, z);
			lines.push_back(line);

		}
		// [48..55] yz 平面の斜め: x を固定し、(y, z) = (t, t) と (t, 3-t) の 2本ずつ。
		for (int x = 0; x < SIZE; x++)
		{
			unsigned long long line1 = 0uLL, line2 = 0uLL;
			for (int yz = 0; yz < SIZE; yz++)
			{
				line1 |= BIT(x, yz, yz);
				line2 |= BIT(x, yz, SIZE - 1 - yz);
			}
			lines.push_back(line1);
			lines.push_back(line2);

		}
		// [56..63] zx 平面の斜め: y を固定し、(x, z) = (t, t) と (t, 3-t) の 2本ずつ。
		for (int y = 0; y < SIZE; y++)
		{
			unsigned long long line1 = 0uLL, line2 = 0uLL;
			for (int zx = 0; zx < SIZE; zx++)
			{
				line1 |= BIT(zx, y, zx);
				line2 |= BIT(zx, y, SIZE - 1 - zx);
			}
			lines.push_back(line1);
			lines.push_back(line2);

		}
		// [64..71] xy 平面の斜め: z を固定し、(x, y) = (t, t) と (t, 3-t) の 2本ずつ。
		for (int z = 0; z < SIZE; z++)
		{
			unsigned long long line1 = 0uLL, line2 = 0uLL;
			for (int xy = 0; xy < SIZE; xy++)
			{
				line1 |= BIT(xy, xy, z);
				line2 |= BIT(xy, SIZE - 1 - xy, z);
			}
			lines.push_back(line1);
			lines.push_back(line2);

		}
		// [72..75] 立体の対角線 4本: x = t に対して y, z をそれぞれ t か 3-t にする組み合わせ。
		{
			unsigned long long line1 = 0uLL, line2 = 0uLL, line3 = 0uLL, line4 = 0uLL;
			for (int xyz = 0; xyz < SIZE; xyz++)
			{
				line1 |= BIT(xyz, xyz, xyz);
				line2 |= BIT(xyz, xyz, SIZE - 1 - xyz);
				line3 |= BIT(xyz, SIZE - 1 - xyz, xyz);
				line4 |= BIT(xyz, SIZE - 1 - xyz, SIZE - 1 - xyz);
			}
			lines.push_back(line1);
			lines.push_back(line2);
			lines.push_back(line3);
			lines.push_back(line4);

		}
		// 本数が 76本ちょうどであること。
		assert(lines.size() == LINES_NUM);

		// LINES に写しながら、各ラインが
		//   - ちょうど 4マスであること
		//   - win() が 4つ並びとして認識すること(win() のシフト演算と表が食い違っていないこと)
		// を確かめる。
		for (int j = 0; j < LINES_NUM; j++)
		{
			LINES[j] = lines[j];
			assert(__builtin_popcountll(LINES[j]) == 4);
			assert(Board::win(LINES[j]) == State::End);
		}
	}
	{//validate move_order
		// move_order(common.hpp)の 3グループを合わせると全 64マスになること
		// (どのマスも探索で必ず候補に上がること)を確かめる。
		unsigned long long mv = 0uLL;
		for(unsigned long long mask: move_order) mv |= mask;
		assert(mv == 0xffffffffffffffffuLL);
	}
}
