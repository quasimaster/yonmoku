# -*- coding: utf-8 -*-
"""調査その8: 核ペア特徴量の粒度をどう取るべきかを比較する。
   A: 4本の棒を合計した本数(実装案。2本)
   B: 棒ごとに分ける(4棒 x {自自, 敵敵} = 8本)   <- 「12パラメータ?」の案
   C: 本数を one-hot(線形性の検証。8本)
   D: 核2マスの全状態を共有テーブルに(6本)
   いずれも制約C 限定(探索が実際に評価する分布)で測る。"""
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
_LUT=np.array([bin(i).count('1') for i in range(256)],dtype=np.uint8)
def pc(a): return _LUT[a.view(np.uint8).reshape(len(a),8)].sum(1)
Me,You=d['Me'],d['You']; occ=Me|You
# 制約C
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
LM=np.array([sum(1<<IDX(*c) for c in l) for l in L],dtype=np.uint64)
z=np.load('out/lines_ab.npz'); A_=z['A']; B_=z['B']
rMe=np.zeros(n,dtype=np.uint64); rYou=np.zeros(n,dtype=np.uint64)
for i in range(76):
    e=LM[i]&~occ
    rMe|=np.where((A_[:,i]==3)&(B_[:,i]==0),e,np.uint64(0))
    rYou|=np.where((B_[:,i]==3)&(A_[:,i]==0),e,np.uint64(0))
hand=((occ<<np.uint64(16))|np.uint64(0xffff))&~occ
CSEL=((hand&rMe)==0)&((hand&rYou)==0)

def bit(a,i): return ((a>>np.uint64(i))&np.uint64(1)).astype(np.int8)
CENTER=[1+4*1, 2+4*1, 1+4*2, 2+4*2]          # 中心4棒(LINES 添字 5,6,9,10)
mm=[];yy=[];st7=[]
for c in CENTER:
    m1,m2=bit(Me,c+16),bit(Me,c+32); y1,y2=bit(You,c+16),bit(You,c+32)
    mm.append(m1&m2); yy.append(y1&y2)
    o1,o2=m1|y1,m2|y2
    s=np.zeros(n,dtype=np.int8)          # 0:未充填 1:z1自のみ 2:z1敵のみ 3:自自 4:自敵 5:敵自 6:敵敵
    s=np.where(o2==0, np.where(o1==0,0,np.where(m1==1,1,2)),
               np.where(m1==1,np.where(m2==1,3,4),np.where(m2==1,5,6))).astype(np.int8)
    st7.append(s)
CM=np.stack(mm,1); CY=np.stack(yy,1)                      # (n,4)
cnt_me=CM.sum(1).astype(np.int16); cnt_you=CY.sum(1).astype(np.int16)
FA=np.stack([cnt_me,cnt_you],1)                                        # A: 2本
FB=np.hstack([CM,CY]).astype(np.int16)                                 # B: 8本(棒ごと)
FC=np.stack([ (cnt_me==k).astype(np.int16) for k in (1,2,3,4)]
           +[ (cnt_you==k).astype(np.int16) for k in (1,2,3,4)],1)     # C: 8本(one-hot)
ST=np.stack(st7,1)
FD=np.stack([ (ST==k).sum(1).astype(np.int16) for k in range(1,7)],1)  # D: 6本(核2マスの全状態)

def fit(X,pp,iters=30,ridge=1e-4):
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

print('核ペアの出現頻度(制約C 限定):')
for s in (0,1):
    for b in (0,1):
        sel=(d['side']==s)&(bucket==b)&CSEL
        print(f"  {'fir' if s==0 else 'sec'} b{b}: 自 0本{100*(cnt_me[sel]==0).mean():5.1f}% "
              f"1本{100*(cnt_me[sel]==1).mean():5.1f}% 2本{100*(cnt_me[sel]==2).mean():4.1f}% "
              f"3本以上{100*(cnt_me[sel]>=3).mean():4.2f}%")
cand=[('A 合計本数(実装案)',FA),('B 棒ごとに分ける',FB),('C 本数の one-hot',FC),('D 核2マスの全状態',FD),
      ('A+B(両方)',np.hstack([FA,FB]))]
for s in (0,1):
    for b in (0,1):
        sel=(d['side']==s)&(bucket==b)&CSEL
        X0=d['f'][sel].astype(np.float64); pp=p[sel]; g=d['game'][sel]
        tr=(g%2==1); te=~tr
        w0=fit(X0[tr],pp[tr]); bte=loss(X0[te],w0,pp[te]); btr=loss(X0[tr],w0,pp[tr])
        print(f"\n=== {'fir' if s==0 else 'sec'} bucket{b}  n={sel.sum()} | base29 train {btr:.6f} test {bte:.6f} ===")
        for nm,F in cand:
            X=np.hstack([X0,F[sel].astype(np.float64)])
            w=fit(X[tr],pp[tr])
            lt=loss(X[te],w,pp[te]); ltr=loss(X[tr],w,pp[tr])
            print(f"  +{nm:<22} {F.shape[1]:>2}本  train {ltr:.6f} ({ltr-btr:+.6f})  test {lt:.6f} ({lt-bte:+.6f})")
