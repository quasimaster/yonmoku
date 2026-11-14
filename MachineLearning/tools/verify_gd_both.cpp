// evaluate_gd_both.hpp が既存の学習用評価関数と完全に一致することを実測で確かめる。
//
//   黒(先手)手番の局面: gd::evaluate_feature()
//                       == evaluate_pointfir_cont_layer_intersection()   (evaluate_gd_alpha.hpp)
//
// 後手側は、白手番の分岐を yonmoku_gradient_descent_second_alpha.cpp:996-1025 から
// そのまま複写しており、それ以外(evaluate_point / continuous / turn>=60 の処理)は
// 先手側と共有なので、上の一致が取れれば残りは白分岐の複写のみが検証対象になる
// (複写の一致は tools/verify_gd_both_text.py がテキストで確認する)。
//
// ビルド:
//   g++ -std=c++17 -O2 -o verify_gd_both.exe MachineLearning/tools/verify_gd_both.cpp

#include "../../code/common.hpp"
#include "../../code/board.hpp"
#include "../evaluate_gd_alpha.hpp"   // 先手学習で使っている現行の評価関数(グローバル)
#include "../evaluate_gd_both.hpp"    // 今回作った統合版(namespace gd)
#include "../console_utf8.hpp"

static void set_global_parameters(const int ps[29])
{
	// evaluate_gd_alpha.hpp 側のパラメータ。main_gd_alpha_all.cpp の特徴量構築部と同じ配り方。
	pb = ps[0], pc = ps[1], pd = ps[2], pe = ps[3];
	pg = ps[4], ph = ps[5], pi = ps[6];
	pj = ps[7], pk = ps[8], pl = ps[9];
	pm = ps[10], pn = ps[11], pr = ps[12], pt = ps[13];
	po = ps[14];
	ppa = ps[15], ppb = ps[16], ppc = ps[17], ppd = ps[18];
	pqa = ps[19], pqb = ps[20], pqc = ps[21], pqd = ps[22];
	ppe = ps[23], ppf = ps[24], ppg = ps[25];
	pqe = ps[26], pqf = ps[27], pqg = ps[28];
}

int main()
{
	//コンソールの出力コードページを UTF-8 に合わせる(日本語の文字化け対策)
	enable_utf8_console();
	init_lines();

	mt19937 r(20260906u);
	uniform_int_distribution<int> dist(-1500, 1500);

	long long checked_black = 0, checked_white = 0, mismatch = 0;

	for (int game = 0; game < 3000; game++)
	{
		Board c;
		for (int mv = 0; mv < 64; mv++)
		{
			const unsigned long long hand = c.valid_move();
			if (!hand) break;

			// 合法手の中から一様ランダムに 1 手選ぶ
			vector<int> idx;
			for (int xyz = 0; xyz < BOARD_SIZE; xyz++) if (hand & 1uLL << xyz) idx.push_back(xyz);
			const int pick = idx[r() % idx.size()];
			c.place(X(pick), Y(pick));

			// 毎局面ランダムな重みで比較する(1 つでも配り間違えていれば落ちる)
			int ps[29];
			for (int i = 0; i < 29; i++) ps[i] = dist(r);
			set_global_parameters(ps);
			gd::set_parameters(ps);

			const int a = gd::evaluate_feature(c);

			if (c.player() == Color::Black)
			{
				const int b = evaluate_pointfir_cont_layer_intersection(c);
				checked_black++;
				if (a != b)
				{
					if (mismatch < 5)
						cout << "MISMATCH(black) game=" << game << " mv=" << mv
						     << " turn=" << c.turn() << " both=" << a << " fir=" << b << endl;
					mismatch++;
				}
			}
			else
			{
				checked_white++;
			}
		}
	}

	cout << "black positions compared = " << checked_black << endl;
	cout << "white positions visited  = " << checked_white << endl;
	cout << "mismatch                 = " << mismatch << endl;
	cout << (mismatch == 0 ? "OK: 先手側は現行実装と完全一致" : "NG") << endl;
	return mismatch == 0 ? 0 : 1;
}
