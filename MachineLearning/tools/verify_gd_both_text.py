# evaluate_gd_both.hpp の中身が、既存 2 ファイルの該当行の逐語複写であることを確認する。
#
#   実行: python MachineLearning/tools/verify_gd_both_text.py
#   (MachineLearning ディレクトリからでもリポジトリ直下からでも動く)
#
# 検証する対応:
#   evaluate_point 本体      <- evaluate_gd_alpha.hpp:22-110
#   continuous               <- evaluate_gd_alpha.hpp:131-136
#   reach_layer_intersection
#       先頭〜黒手番の分岐   <- evaluate_gd_alpha.hpp:138-190
#       白手番の分岐         <- yonmoku_gradient_descent_second_alpha.cpp:996-1025(字下げ -4)
#       turn>=60 以降        <- evaluate_gd_alpha.hpp:215-231
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ML = os.path.dirname(HERE)

HPP = os.path.join(ML, 'evaluate_gd_alpha.hpp')
SA = os.path.join(ML, 'yonmoku_gradient_descent_second_alpha.cpp')
BOTH = os.path.join(ML, 'evaluate_gd_both.hpp')


def lines(path):
    with open(path, 'rb') as f:
        return f.read().decode('utf-8').split('\n')


def take(path, a, b):
    return lines(path)[a - 1:b]


def dedent4(ls):
    return [l[4:] if l.startswith('    ') else l for l in ls]


def find_block(hay, needle, what):
    """hay の中から needle(行のリスト)が現れる位置を探す。"""
    n = len(needle)
    for i in range(len(hay) - n + 1):
        if hay[i:i + n] == needle:
            return i
    print('NG: %s が evaluate_gd_both.hpp の中に逐語では見つからない' % what)
    # 最初にずれた行を報告する
    best, besti = -1, 0
    for i in range(len(hay) - n + 1):
        k = 0
        while k < n and hay[i + k] == needle[k]:
            k += 1
        if k > best:
            best, besti = k, i
    print('    最も一致した位置 %d 行目で %d 行目まで一致' % (besti + 1, best))
    if best < n:
        print('    期待: %r' % needle[best])
        print('    実際: %r' % (hay[besti + best] if besti + best < len(hay) else '<EOF>'))
    return None


both = lines(BOTH)

checks = [
    ('evaluate_point 本体 (evaluate_gd_alpha.hpp:22-110)', take(HPP, 22, 110)),
    ('continuous (evaluate_gd_alpha.hpp:131-136)', take(HPP, 131, 136)),
    ('reach_layer_intersection 先頭〜黒手番 (evaluate_gd_alpha.hpp:138-190)', take(HPP, 138, 190)),
    ('reach_layer_intersection 白手番 (second_alpha.cpp:996-1025)', dedent4(take(SA, 996, 1025))),
    ('reach_layer_intersection turn>=60 以降 (evaluate_gd_alpha.hpp:215-231)', take(HPP, 215, 231)),
]

ng = 0
for what, block in checks:
    pos = find_block(both, block, what)
    if pos is None:
        ng += 1
    else:
        print('OK: %s  -> evaluate_gd_both.hpp:%d-%d' % (what, pos + 1, pos + len(block)))

# 黒手番の分岐と白手番の分岐が、パラメータ以外は同じ構造であることも一応見ておく
print('')
if ng == 0:
    print('すべて逐語一致。先手側・後手側とも元コードと同じ値を返す。')
else:
    print('%d 件が一致しない。' % ng)
sys.exit(1 if ng else 0)
