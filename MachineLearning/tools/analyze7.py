# -*- coding: utf-8 -*-
"""調査その7: 「制約C を満たす局面だけで学習させると精度が上がるか」を直接測る。
   学習集合 = 全局面 / 制約C限定 の 2 通り、テスト = 制約C限定 / 全局面 の 2 通り。"""
import numpy as np
PNUM=29
DT=np.dtype([('Me','<u8'),('You','<u8'),('game','<i4'),('teacher','<i4'),
             ('ply','<i2'),('result','i1'),('side','i1'),('f','<i2',(PNUM,))])
d=np.fromfile('out/probe_ver8_2.bin',dtype=DT); n=len(d)
turn=d['ply'].astype(np.int32)+2
bucket=np.where(d['side']==0,(turn-4)//14,(turn-5)//14)
t=d['teacher'].astype(np.float64)
with np.errstate(over='ignore'):
    p=np.where(t<-1840,0.99,np.where(t>1840,0.01,1.0-1.0/(1.0+np.exp(-t/400.0))))
sat=np.abs(t)>1840     # 教師値が飽和している(= 勝敗がほぼ決まっている)局面
_LUT=np.array([bin(i).count('1') for i in range(256)],dtype=np.uint8)
def pc(a): return _LUT[a.view(np.uint8).reshape(len(a),8)].sum(1)
Me,You=d['Me'],d['You']; occ=Me|You
S=4
def IDX(x,y,z): return x+y*S+z*S*S
L=[]
for x in range(S):
    for y in range(S): L.append([(x,y,z) for z in range(S)])
for y in range(S):
    for z in range(S): L.append([(x,y,z) for x in range(S)])
for z in range(S):
    for x in range(S): L.append([(x,y,z) for y in range(S)])
for x in range(S):
    L.append([(x,i,i) for i in range(S)]); L.append([(x,i,S-1-i) for i in range(S)])
for y in range(S):
    L.append([(i,y,i) for i in range(S)]); L.append([(i,y,S-1-i) for i in range(S)])
for z in range(S):
    L.append([(i,i,z) for i in range(S)]); L.append([(i,S-1-i,z) for i in range(S)])
L.append([(i,i,i) for i in range(S)]);     L.append([(i,i,S-1-i) for i in range(S)])
L.append([(i,S-1-i,i) for i in range(S)]); L.append([(i,S-1-i,S-1-i) for i in range(S)])
LMASK=np.array([sum(1<<IDX(*c) for c in l) for l in L],dtype=np.uint64)
z=np.load('out/lines_ab.npz'); A=z['A']; B=z['B']
rMe=np.zeros(n,dtype=np.uint64); rYou=np.zeros(n,dtype=np.uint64)
for i in range(76):
    e=LMASK[i]&~occ
    rMe |= np.where((A[:,i]==3)&(B[:,i]==0),e,np.uint64(0))
    rYou|= np.where((B[:,i]==3)&(A[:,i]==0),e,np.uint64(0))
hand=((occ<<np.uint64(16))|np.uint64(0xffff))&~occ
C=((hand&rMe)==0)&((hand&rYou)==0)
# 内訳
mine=((hand&rMe)!=0); yours=((hand&rYou)!=0)
print(f"全 {n} 局面: 制約C {C.mean()*100:.1f}% / 自分に即勝ち手あり {mine.mean()*100:.1f}% / 相手に即勝ち手あり {yours.mean()*100:.1f}%")
print(f"教師値が飽和(|t|>1840) している割合: 全体 {sat.mean()*100:.1f}% / 制約C内 {sat[C].mean()*100:.1f}% / 制約C外 {sat[~C].mean()*100:.1f}%")

def fit(X,pp,iters=30,ridge=1e-6):
    w=np.zeros(X.shape[1])
    for _ in range(iters):
        q=1.0/(1.0+np.exp(-(X@w)/400.0)); g=X.T@(q-pp)/400.0
        H=X.T@(X*(q*(1-q)/160000.0)[:,None])+ridge*np.eye(X.shape[1])
        s=np.linalg.solve(H,g); w-=s
        if np.max(np.abs(s))<1e-9: break
    return w
def loss(X,w,pp):
    q=np.clip(1.0/(1.0+np.exp(-(X@w)/400.0)),1e-12,1-1e-12)
    return float((-pp*np.log(q)-(1-pp)*np.log1p(-q)).sum())/len(pp)

print("\n学習集合を変えたときのテスト loss(いずれも同じテスト局面で比較)")
print("                       | テスト=制約C限定(探索が実際に評価する分布) | テスト=全局面")
print("side/bkt  学習集合      |      loss        フィルタ無しとの差       |   loss")
for s in (0,1):
    for b in (0,1):
        base=(d['side']==s)&(bucket==b)
        g=d['game']
        tr_all=base&(g%2==1); te_all=base&(g%2==0)
        tr_C  =tr_all&C;      te_C  =te_all&C
        X=d['f'].astype(np.float64)
        w_all=fit(X[tr_all],p[tr_all])
        w_C  =fit(X[tr_C],  p[tr_C])
        lC_all=loss(X[te_C],w_all,p[te_C]); lC_C=loss(X[te_C],w_C,p[te_C])
        lA_all=loss(X[te_all],w_all,p[te_all]); lA_C=loss(X[te_all],w_C,p[te_all])
        nm=f"{'fir' if s==0 else 'sec'} b{b}"
        print(f"{nm:9s} 全局面({tr_all.sum():6d})  |   {lC_all:.6f}          (基準)         | {lA_all:.6f}")
        print(f"{nm:9s} 制約C ({tr_C.sum():6d})  |   {lC_C:.6f}      {lC_C-lC_all:+.6f}        | {lA_C:.6f} ({lA_C-lA_all:+.6f})")
        # 参考: 飽和局面を除くフィルタ
        tr_S=tr_all&~sat
        w_S=fit(X[tr_S],p[tr_S]); lC_S=loss(X[te_C],w_S,p[te_C])
        print(f"{nm:9s} 参考:飽和除({tr_S.sum():6d})|   {lC_S:.6f}      {lC_S-lC_all:+.6f}        |")
