# -*- coding: utf-8 -*-
"""調査その6: 探索が実際に葉評価を呼ぶ局面(制約C: 即座に置けるマスの上に双方のリーチが無い)
              に限定して測り直す。ai_player_pvs_inc_id.hpp:147-158 の条件。"""
import numpy as np, os
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
CLS=np.zeros(76,dtype=int); CLS[0:16]=0; CLS[16:48]=1; CLS[48:64]=2; CLS[64:72]=3; CLS[72:76]=4
z=np.load('out/lines_ab.npz'); A=z['A']; B=z['B']
rMe=np.zeros(n,dtype=np.uint64); rYou=np.zeros(n,dtype=np.uint64)
for i in range(76):
    e=LMASK[i]&~occ
    rMe |= np.where((A[:,i]==3)&(B[:,i]==0),e,np.uint64(0))
    rYou|= np.where((B[:,i]==3)&(A[:,i]==0),e,np.uint64(0))
hand=((occ<<np.uint64(16))|np.uint64(0xffff))&~occ
CSEL=((hand&rMe)==0)&((hand&rYou)==0)
print(f'制約C を満たす局面: {CSEL.mean()*100:.1f}%  ({CSEL.sum()} / {n})')
for s in (0,1):
    for b in (0,1):
        sel=(d['side']==s)&(bucket==b)
        print(f"   side{s} bucket{b}: {100*CSEL[sel].mean():.1f}%")

# --- 候補 ---
H=np.zeros((n,16),dtype=np.int8)
for c in range(16):
    H[:,c]=sum(((occ>>np.uint64(c+16*zz))&np.uint64(1)).astype(np.int8) for zz in range(4))
CC1=np.uint64(0x0000000006600000); CORE=np.uint64(0x0000066006600000)
C1=np.stack([pc(Me&CC1&(Me>>np.uint64(16))),pc(You&CC1&(You>>np.uint64(16)))],1).astype(np.int16)
C2=np.stack([pc(Me&CORE),pc(You&CORE)],1).astype(np.int16)
# D4': 即勝ち2本を除いた 3 本(毒手 自/敵 と 自由なマス)
D4=np.stack([pc(hand&(rYou>>np.uint64(16))),pc(hand&(rMe>>np.uint64(16))),
             pc(hand&~((rMe>>np.uint64(16))|(rYou>>np.uint64(16))))],1).astype(np.int16)
# D1 gap
Gm=np.zeros((n,4),dtype=np.int16);Gy=np.zeros((n,4),dtype=np.int16)
Rm=np.zeros((n,4),dtype=np.int16);Ry=np.zeros((n,4),dtype=np.int16)
for i in range(76):
    zs=np.array([c[2] for c in L[i]]); cs=np.array([c[0]+4*c[1] for c in L[i]])
    g=np.stack([zs[j]-H[:,cs[j]].astype(np.int16) for j in range(4)],1)
    gmin=np.where(g>=0,g,np.int16(99)).min(1)
    m2=(A[:,i]==2)&(B[:,i]==0); y2=(A[:,i]==0)&(B[:,i]==2)
    m3=(A[:,i]==3)&(B[:,i]==0); y3=(A[:,i]==0)&(B[:,i]==3)
    for k in range(4):
        q=(gmin==k); Gm[:,k]+=(m2&q); Gy[:,k]+=(y2&q); Rm[:,k]+=(m3&q); Ry[:,k]+=(y3&q)
D1=np.hstack([Gm,Gy,Rm,Ry])
ST=[(a,b) for a in range(4) for b in range(4) if 0<a+b<=4]
E2=np.hstack([np.stack([((A[:,np.where(CLS==c)[0]]==ka)&(B[:,np.where(CLS==c)[0]]==kb)).sum(1).astype(np.int16)
                        for (ka,kb) in ST],1) for c in range(5)])
def bit(a,i): return ((a>>np.uint64(i))&np.uint64(1)).astype(np.int64)
COLS={'center':[(1,1),(1,2),(2,1),(2,2)],'corner':[(0,0),(0,3),(3,0),(3,3)],
      'edge':[(x,y) for x in range(4) for y in range(4) if (x in (0,3))!=(y in (0,3))]}
cst=[]
for name,cs in COLS.items():
    st=np.zeros((n,31),dtype=np.int16)
    for (x,y) in cs:
        c=x+4*y
        mb=[bit(Me,c+16*zz) for zz in range(4)]; yb=[bit(You,c+16*zz) for zz in range(4)]
        h=sum(mb[zz]|yb[zz] for zz in range(4)); val=mb[0]+2*mb[1]+4*mb[2]+8*mb[3]
        st[np.arange(n),(1<<h)-1+(val&((1<<h)-1))]+=1
    cst.append(st[:,1:])
C456=np.hstack(cst)
def fit(X,pp,iters=30,ridge=1e-4):
    w=np.zeros(X.shape[1])
    for _ in range(iters):
        q=1.0/(1.0+np.exp(-(X@w)/400.0)); g=X.T@(q-pp)/400.0
        Hs=X.T@(X*(q*(1-q)/160000.0)[:,None])+ridge*np.eye(X.shape[1])
        st=np.linalg.solve(Hs,g); w-=st
        if np.max(np.abs(st))<1e-9: break
    return w
def loss(X,w,pp):
    q=np.clip(1.0/(1.0+np.exp(-(X@w)/400.0)),1e-12,1-1e-12)
    return float((-pp*np.log(q)-(1-pp)*np.log1p(-q)).sum())
NOSTD=[i for i in range(PNUM) if i>=4]
cand=[('C1 案①核ペア(2)',range(PNUM),C1),
      ('C1+C2 核ペア+核数(4)',range(PNUM),np.hstack([C1,C2])),
      ("D4' 毒手・自由マス(3)",range(PNUM),D4),
      ('D1 gap(16)',range(PNUM),D1),
      ('C456 棒表(90)',range(PNUM),C456),
      ('E2 線種別2次元表(65,std置換)',NOSTD,E2),
      ("E2+C456+D1+D4'(174)",NOSTD,np.hstack([E2,C456,D1,D4]))]
for s in (0,1):
    for b in (0,1):
        sel=(d['side']==s)&(bucket==b)&CSEL
        X0=d['f'][sel].astype(np.float64); pp=p[sel]; g=d['game'][sel]
        tr=(g%2==1); te=~tr
        w0=fit(X0[tr],pp[tr]); bte=loss(X0[te],w0,pp[te])/te.sum()
        print(f"\n=== 制約C限定 side={'fir' if s==0 else 'sec'} bucket{b} n={sel.sum()} | base29 {bte:.6f} ===")
        for nm,keep,F in cand:
            X=np.hstack([X0[:,list(keep)],F[sel].astype(np.float64)])
            w=fit(X[tr],pp[tr]); lt=loss(X[te],w,pp[te])/te.sum()
            print(f"  {nm:<30} k={X.shape[1]:<4} {lt:.6f} ({lt-bte:+.6f})")
