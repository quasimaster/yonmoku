# -*- coding: utf-8 -*-
"""probe_ver8_2.bin を読み、候補特徴量の「現行29パラメータに対する上乗せ効果」を測る。
   学習コード・対局コードには一切触れない、調査専用スクリプト。"""
import numpy as np, sys, os

PNUM = 29
DT = np.dtype([('Me','<u8'),('You','<u8'),('game','<i4'),('teacher','<i4'),
               ('ply','<i2'),('result','i1'),('side','i1'),('f','<i2',(PNUM,))])

d = np.fromfile('out/probe_ver8_2.bin', dtype=DT)
print('rows', len(d), 'games', d['game'].max())
turn = d['ply'].astype(np.int32) + 2
bucket = np.where(d['side']==0, (turn-4)//14, (turn-5)//14)
print('side/bucket counts:')
for s in (0,1):
    for b in (0,1):
        print('  side',s,'bucket',b, int(((d['side']==s)&(bucket==b)).sum()))
print('result dist', np.bincount(d['result']+1))

# ---------- popcount ----------
_LUT = np.array([bin(i).count('1') for i in range(256)], dtype=np.uint8)
def pc(a):
    return _LUT[a.view(np.uint8).reshape(len(a),8)].sum(1).astype(np.int16)

Me, You = d['Me'], d['You']

def bits(a, idx):   # idx: list of bit positions -> (n,len) uint8 0/1
    return np.stack([((a >> np.uint64(i)) & np.uint64(1)).astype(np.uint8) for i in idx], axis=1)

# ---------- 候補特徴量 ----------
CORE = np.uint64(0x0000066006600000)          # 核8マス
CC1  = np.uint64(0x0000000006600000)          # 中心4棒の z=1
feats = {}

# C1 ユーザ案1: 中心棒で核2マスが同色
feats['C1_corepair_me']  = pc(Me & CC1 & (Me >> np.uint64(16)))
feats['C1_corepair_you'] = pc(You & CC1 & (You >> np.uint64(16)))
# C2 対照: 核の占有数
feats['C2_core_me']  = pc(Me & CORE)
feats['C2_core_you'] = pc(You & CORE)

# 棒(16本)の状態 one-hot。state = (2^h - 1) + value(me bits)
COLS = {'center':[(1,1),(1,2),(2,1),(2,2)],
        'corner':[(0,0),(0,3),(3,0),(3,3)],
        'edge'  :[(x,y) for x in range(4) for y in range(4)
                  if (x in (0,3)) != (y in (0,3))]}
n = len(d)
col_state = {}
for name, cs in COLS.items():
    st = np.zeros((n, 31), dtype=np.int16)
    st3 = np.zeros((n, 15), dtype=np.int16)   # 下3マスだけ見た版
    for (x,y) in cs:
        c = x + 4*y
        mb = bits(Me,  [c, c+16, c+32, c+48])
        yb = bits(You, [c, c+16, c+32, c+48])
        ob = mb | yb
        h  = ob.sum(1).astype(np.int64)
        val = (mb[:,0]*1 + mb[:,1]*2 + mb[:,2]*4 + mb[:,3]*8).astype(np.int64)
        idx = (1 << h) - 1 + (val & ((1 << h) - 1))
        st[np.arange(n), idx] += 1
        h3  = np.minimum(h, 3)
        val3 = (mb[:,0]*1 + mb[:,1]*2 + mb[:,2]*4).astype(np.int64)
        idx3 = (1 << h3) - 1 + (val3 & ((1 << h3) - 1))
        st3[np.arange(n), idx3] += 1
    col_state[name] = (st, st3)

# ---------- 教師ラベル ----------
t = d['teacher'].astype(np.float64)
p = np.where(t < -1840, 0.99, np.where(t > 1840, 0.01, 1.0 - 1.0/(1.0+np.exp(-t/400.0))))

def fit(X, p, iters=25, ridge=1e-6):
    """soft-label logistic:  q = sigmoid(X w / 400)"""
    w = np.zeros(X.shape[1])
    for _ in range(iters):
        s = X @ w / 400.0
        q = 1.0/(1.0+np.exp(-s))
        g = X.T @ (q - p) / 400.0
        wgt = q*(1-q)/(400.0**2)
        H = X.T @ (X * wgt[:,None]) + ridge*np.eye(X.shape[1])
        step = np.linalg.solve(H, g)
        w -= step
        if np.max(np.abs(step)) < 1e-9: break
    return w

def loss(X, w, p):
    s = X @ w / 400.0
    q = 1.0/(1.0+np.exp(-s))
    q = np.clip(q, 1e-12, 1-1e-12)
    return float((-p*np.log(q) - (1-p)*np.log1p(-q)).sum())

def run(sel, label, extra):
    X0 = d['f'][sel].astype(np.float64)
    pp = p[sel]
    g  = d['game'][sel]
    tr = (g % 2 == 1); te = ~tr
    res = {}
    base_w = fit(X0[tr], pp[tr])
    base_te = loss(X0[te], base_w, pp[te]) / te.sum()
    base_tr = loss(X0[tr], base_w, pp[tr]) / tr.sum()
    print(f'\n=== {label}  n={sel.sum()}  (train {tr.sum()} / test {te.sum()}) ===')
    print(f'  base29        train {base_tr:.6f}  test {base_te:.6f}')
    for nm, F in extra:
        X = np.hstack([X0, F[sel].astype(np.float64)])
        w = fit(X[tr], pp[tr])
        lt = loss(X[te], w, pp[te]) / te.sum()
        ltr = loss(X[tr], w, pp[tr]) / tr.sum()
        print(f'  +{nm:<22} k={F.shape[1]:<3} train {ltr:.6f} ({ltr-base_tr:+.6f})  test {lt:.6f} ({lt-base_te:+.6f})')
        res[nm] = lt - base_te
    return res

C1 = np.stack([feats['C1_corepair_me'], feats['C1_corepair_you']], 1)
C2 = np.stack([feats['C2_core_me'],     feats['C2_core_you']], 1)
extra = [
    ('C1 core-pair(2)',       C1),
    ('C2 core-count(2)',      C2),
    ('C1+C2 (4)',             np.hstack([C1,C2])),
    ('C3 center bottom3(14)', col_state['center'][1][:,1:]),
    ('C4 center full(30)',    col_state['center'][0][:,1:]),
    ('C5 corner full(30)',    col_state['corner'][0][:,1:]),
    ('C6 edge full(30)',      col_state['edge'][0][:,1:]),
    ('C4+C5+C6 (90)',         np.hstack([col_state['center'][0][:,1:],
                                         col_state['corner'][0][:,1:],
                                         col_state['edge'][0][:,1:]])),
]
out = {}
for s in (0,1):
    for b in (0,1):
        sel = (d['side']==s) & (bucket==b)
        out[(s,b)] = run(sel, f"side={'fir' if s==0 else 'sec'} bucket{b} turn{turn[sel].min()}-{turn[sel].max()}", extra)
