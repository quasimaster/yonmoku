# -*- coding: utf-8 -*-
"""調査その2: (a) 既存パラメータ群のアブレーションで loss のスケールを測る
             (b) 混在ライン(死にライン)テーブル C7 の効果
             (c) 棒テーブルを色反対称に制約した版(半分のパラメータ)"""
import numpy as np
PNUM = 29
DT = np.dtype([('Me','<u8'),('You','<u8'),('game','<i4'),('teacher','<i4'),
               ('ply','<i2'),('result','i1'),('side','i1'),('f','<i2',(PNUM,))])
d = np.fromfile('out/probe_ver8_2.bin', dtype=DT)
n = len(d)
turn = d['ply'].astype(np.int32) + 2
bucket = np.where(d['side']==0, (turn-4)//14, (turn-5)//14)
t = d['teacher'].astype(np.float64)
with np.errstate(over='ignore'):
    p = np.where(t < -1840, 0.99, np.where(t > 1840, 0.01, 1.0 - 1.0/(1.0+np.exp(-t/400.0))))

_LUT = np.array([bin(i).count('1') for i in range(256)], dtype=np.uint8)
def pc(a): return _LUT[a.view(np.uint8).reshape(len(a),8)].sum(1)
Me, You = d['Me'], d['You']

def fit(X, p, iters=25, ridge=1e-6):
    w = np.zeros(X.shape[1])
    for _ in range(iters):
        s = X @ w / 400.0
        q = 1.0/(1.0+np.exp(-s))
        g = X.T @ (q - p) / 400.0
        H = X.T @ (X * (q*(1-q)/160000.0)[:,None]) + ridge*np.eye(X.shape[1])
        st = np.linalg.solve(H, g); w -= st
        if np.max(np.abs(st)) < 1e-9: break
    return w
def loss(X, w, p):
    q = np.clip(1.0/(1.0+np.exp(-(X @ w)/400.0)), 1e-12, 1-1e-12)
    return float((-p*np.log(q) - (1-p)*np.log1p(-q)).sum())

# ---------- LINES(board.hpp init_lines と同順)----------
S=4
def IDX(x,y,z): return x+y*S+z*S*S
L=[]
for x in range(S):
    for y in range(S): L.append([IDX(x,y,z) for z in range(S)])
for y in range(S):
    for z in range(S): L.append([IDX(x,y,z) for x in range(S)])
for z in range(S):
    for x in range(S): L.append([IDX(x,y,z) for y in range(S)])
for x in range(S):
    L.append([IDX(x,i,i) for i in range(S)]); L.append([IDX(x,i,S-1-i) for i in range(S)])
for y in range(S):
    L.append([IDX(i,y,i) for i in range(S)]); L.append([IDX(i,y,S-1-i) for i in range(S)])
for z in range(S):
    L.append([IDX(i,i,z) for i in range(S)]); L.append([IDX(i,S-1-i,z) for i in range(S)])
L.append([IDX(i,i,i) for i in range(S)]);       L.append([IDX(i,i,S-1-i) for i in range(S)])
L.append([IDX(i,S-1-i,i) for i in range(S)]);   L.append([IDX(i,S-1-i,S-1-i) for i in range(S)])
assert len(L)==76
LMASK = np.array([sum(1<<c for c in l) for l in L], dtype=np.uint64)

# ---------- C7: 混在ライン内訳 ----------
MIX = [(1,1),(2,1),(1,2),(3,1),(1,3),(2,2)]
C7 = np.zeros((n, len(MIX)), dtype=np.int16)
for i in range(76):
    a = pc(Me & LMASK[i]); b = pc(You & LMASK[i])
    for k,(ka,kb) in enumerate(MIX):
        C7[:,k] += ((a==ka)&(b==kb)).astype(np.int16)
print('C7 mean per state:', C7.mean(0).round(3))

# ---------- 棒テーブル(反対称制約版)----------
def flip_state(idx):
    h = 0
    while (1<<(h+1))-1 <= idx: h += 1      # 2^h-1 <= idx < 2^(h+1)-1
    val = idx - ((1<<h)-1)
    return ((1<<h)-1) + (~val & ((1<<h)-1))
PAIRS = []
seen=set()
for s in range(31):
    f = flip_state(s)
    if s==f or s in seen: continue
    seen.add(s); seen.add(f); PAIRS.append((s,f))
assert len(PAIRS)==15
COLS = {'center':[(1,1),(1,2),(2,1),(2,2)],
        'corner':[(0,0),(0,3),(3,0),(3,3)],
        'edge'  :[(x,y) for x in range(4) for y in range(4) if (x in (0,3)) != (y in (0,3))]}
def bit(a,i): return ((a >> np.uint64(i)) & np.uint64(1)).astype(np.int64)
colst = {}
for name, cs in COLS.items():
    st = np.zeros((n,31), dtype=np.int16)
    for (x,y) in cs:
        c = x+4*y
        mb=[bit(Me,c+16*z) for z in range(4)]; yb=[bit(You,c+16*z) for z in range(4)]
        h = sum(mb[z]|yb[z] for z in range(4))
        val = mb[0]+2*mb[1]+4*mb[2]+8*mb[3]
        idx = (1<<h)-1 + (val & ((1<<h)-1))
        st[np.arange(n), idx] += 1
    colst[name]=st
def anti(st):   # 反対称: 各ペアで count[s] - count[flip(s)]
    return np.stack([st[:,s].astype(np.int16)-st[:,f].astype(np.int16) for s,f in PAIRS],1)

GROUPS = {'stdweight(4)':list(range(0,4)), 'layer(6)':list(range(4,10)),
          'intersection(4)':list(range(10,14)), 'continuous(1)':[14],
          'makeT(8)':list(range(15,23)), 'conti_makeT(6)':list(range(23,29))}

extra = [
 ('C7 mixed-line(6)',      C7),
 ('C4a center anti(15)',   anti(colst['center'])),
 ('C4 center full(30)',    colst['center'][:,1:]),
 ('C456 anti(45)',         np.hstack([anti(colst['center']),anti(colst['corner']),anti(colst['edge'])])),
 ('C456 full(90)',         np.hstack([colst['center'][:,1:],colst['corner'][:,1:],colst['edge'][:,1:]])),
 ('C7+C456anti(51)',       np.hstack([C7,anti(colst['center']),anti(colst['corner']),anti(colst['edge'])])),
]

for s in (0,1):
    for b in (0,1):
        sel = (d['side']==s)&(bucket==b)
        X0 = d['f'][sel].astype(np.float64); pp=p[sel]; g=d['game'][sel]
        tr = (g%2==1); te=~tr
        w0 = fit(X0[tr],pp[tr]); b_te = loss(X0[te],w0,pp[te])/te.sum()
        print(f"\n=== side={'fir' if s==0 else 'sec'} bucket{b} n={sel.sum()} ===")
        print(f"  base29                    test {b_te:.6f}")
        print("  --- アブレーション(その群を外したときの悪化) ---")
        for nm, idxs in GROUPS.items():
            keep = [i for i in range(PNUM) if i not in idxs]
            Xa = X0[:,keep]
            wa = fit(Xa[tr],pp[tr]); la = loss(Xa[te],wa,pp[te])/te.sum()
            print(f"  -{nm:<24} test {la:.6f} ({la-b_te:+.6f})")
        print("  --- 追加候補(改善) ---")
        for nm,F in extra:
            X = np.hstack([X0, F[sel].astype(np.float64)])
            w = fit(X[tr],pp[tr]); lt = loss(X[te],w,pp[te])/te.sum()
            print(f"  +{nm:<24} test {lt:.6f} ({lt-b_te:+.6f})")
