# -*- coding: utf-8 -*-
"""調査その4: ライン種別分割 stdweight / 2次元(自石数,敵石数)テーブル /
             「あと何手で置けるか」(gap)/ 強制手・毒手 の各候補を測る。"""
import numpy as np, os
PNUM=29
DT = np.dtype([('Me','<u8'),('You','<u8'),('game','<i4'),('teacher','<i4'),
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
# ライン種別: 0=縦棒(16) 1=水平軸(32) 2=垂直面斜め(16) 3=水平面斜め(8) 4=空間対角(4)
CLS=np.zeros(76,dtype=int); CLS[0:16]=0; CLS[16:48]=1; CLS[48:64]=2; CLS[64:72]=3; CLS[72:76]=4
CLSN=['V縦棒','H水平軸','Dv垂直面斜め','Dh水平面斜め','S空間対角']

CACHE='out/lines_ab.npz'
if os.path.exists(CACHE):
    z=np.load(CACHE); A=z['A']; B=z['B']
else:
    A=np.zeros((n,76),dtype=np.int8); B=np.zeros((n,76),dtype=np.int8)
    for i in range(76):
        A[:,i]=pc(Me&LMASK[i]); B[:,i]=pc(You&LMASK[i])
    np.savez(CACHE,A=A,B=B)
print('lines done')

# 列の高さ
H=np.zeros((n,16),dtype=np.int8)
for c in range(16):
    H[:,c]=sum(((occ>>np.uint64(c+16*zz))&np.uint64(1)).astype(np.int8) for zz in range(4))

# ---- E1: ライン種別 x 現行4状態 ----
def statecount(sel_cls):
    cols=[]
    idx=np.where(CLS==sel_cls)[0]
    a=A[:,idx]; b=B[:,idx]
    for (ka,kb) in [(2,0),(1,0),(0,1),(0,2)]:
        cols.append(((a==ka)&(b==kb)).sum(1).astype(np.int16))
    return np.stack(cols,1)
E1=np.hstack([statecount(c) for c in range(5)])          # 20本
# ---- E2: ライン種別 x (自,敵) 全13状態 ----
ST=[(a,b) for a in range(4) for b in range(4) if 0<a+b<=4]
def statecount2(sel_cls):
    idx=np.where(CLS==sel_cls)[0]; a=A[:,idx]; b=B[:,idx]
    return np.stack([((a==ka)&(b==kb)).sum(1).astype(np.int16) for (ka,kb) in ST],1)
E2=np.hstack([statecount2(c) for c in range(5)])          # 65本
# ---- C7: 種別を分けない混在テーブルのみ(再掲) ----
MIX=[(1,1),(2,1),(1,2),(3,1),(1,3),(2,2)]
C7=np.stack([((A==ka)&(B==kb)).sum(1).astype(np.int16) for (ka,kb) in MIX],1)

# ---- D1: 「あと何手で置けるか」(gap) ----
gapfeat=[]
Gmin_me=np.zeros((n,4),dtype=np.int16); Gmin_you=np.zeros((n,4),dtype=np.int16)
Gr_me=np.zeros((n,4),dtype=np.int16);   Gr_you=np.zeros((n,4),dtype=np.int16)
for i in range(76):
    cells=L[i]
    zs=np.array([c[2] for c in cells]); cs=np.array([c[0]+4*c[1] for c in cells])
    g=np.stack([zs[j]-H[:,cs[j]].astype(np.int16) for j in range(4)],1)   # >0 なら空き(gap)
    empt=g>=0
    gmask=np.where(empt,g,np.int16(99))
    gmin=gmask.min(1)
    m2=(A[:,i]==2)&(B[:,i]==0); y2=(A[:,i]==0)&(B[:,i]==2)
    m3=(A[:,i]==3)&(B[:,i]==0); y3=(A[:,i]==0)&(B[:,i]==3)
    for k in range(4):
        sel=(gmin==k)
        Gmin_me[:,k]+= (m2&sel); Gmin_you[:,k]+= (y2&sel)
        Gr_me[:,k]  += (m3&sel); Gr_you[:,k]  += (y3&sel)
D1=np.hstack([Gmin_me,Gmin_you,Gr_me,Gr_you])   # 16本
print('gap done')

# ---- D4: 即勝ち手・毒手(打つと上で相手が勝つ) ----
rMe=np.zeros(n,dtype=np.uint64); rYou=np.zeros(n,dtype=np.uint64)
for i in range(76):
    e=LMASK[i]&~occ
    rMe |= np.where((A[:,i]==3)&(B[:,i]==0), e, np.uint64(0))
    rYou|= np.where((B[:,i]==3)&(A[:,i]==0), e, np.uint64(0))
playable=((occ<<np.uint64(16))|np.uint64(0xffff))&~occ
D4=np.stack([pc(playable&rMe), pc(playable&rYou),
             pc(playable&(rYou>>np.uint64(16))), pc(playable&(rMe>>np.uint64(16))),
             pc(playable&~(rMe|rYou|(rMe>>np.uint64(16))|(rYou>>np.uint64(16))))],1).astype(np.int16)
print('threat done')

# ---- 棒テーブル(C456) ----
def bit(a,i): return ((a>>np.uint64(i))&np.uint64(1)).astype(np.int64)
COLS={'center':[(1,1),(1,2),(2,1),(2,2)],'corner':[(0,0),(0,3),(3,0),(3,3)],
      'edge':[(x,y) for x in range(4) for y in range(4) if (x in (0,3))!=(y in (0,3))]}
colst={}
for name,cs in COLS.items():
    st=np.zeros((n,31),dtype=np.int16)
    for (x,y) in cs:
        c=x+4*y
        mb=[bit(Me,c+16*zz) for zz in range(4)]; yb=[bit(You,c+16*zz) for zz in range(4)]
        h=sum(mb[zz]|yb[zz] for zz in range(4)); val=mb[0]+2*mb[1]+4*mb[2]+8*mb[3]
        st[np.arange(n),(1<<h)-1+(val&((1<<h)-1))]+=1
    colst[name]=st[:,1:]
C456=np.hstack([colst['center'],colst['corner'],colst['edge']])

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

BASE_KEEP=[i for i in range(PNUM)]
NOSTD=[i for i in range(PNUM) if i>=4]     # stdweight 4本を外した残り25本
cand=[('E1 線種別std(20,std4置換)', NOSTD, E1),
      ('E2 線種別2次元表(65,std4置換)', NOSTD, E2),
      ('C7 混在表(6)', BASE_KEEP, C7),
      ('D1 gap(16)', BASE_KEEP, D1),
      ('D4 強制手/毒手(5)', BASE_KEEP, D4),
      ('C456 棒表(90)', BASE_KEEP, C456),
      ('E2+C456 (155,std4置換)', NOSTD, np.hstack([E2,C456])),
      ('E2+C456+D1+D4 (176)', NOSTD, np.hstack([E2,C456,D1,D4])),
      ]
for s in (0,1):
    for b in (0,1):
        sel=(d['side']==s)&(bucket==b)
        X0=d['f'][sel].astype(np.float64); pp=p[sel]; g=d['game'][sel]
        tr=(g%2==1); te=~tr
        w0=fit(X0[tr],pp[tr]); b_te=loss(X0[te],w0,pp[te])/te.sum()
        print(f"\n=== side={'fir' if s==0 else 'sec'} bucket{b} n={sel.sum()} | base29 test {b_te:.6f} ===")
        for nm,keep,F in cand:
            X=np.hstack([X0[:,keep],F[sel].astype(np.float64)])
            w=fit(X[tr],pp[tr]); lt=loss(X[te],w,pp[te])/te.sum()
            print(f"  {nm:<28} k={X.shape[1]:<4} test {lt:.6f} ({lt-b_te:+.6f})")
