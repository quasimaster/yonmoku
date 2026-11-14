# -*- coding: utf-8 -*-
"""調査その5: 案①の出現頻度と学習された重みの大きさ、中心棒パターン表の中身を見る。"""
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
Me,You=d['Me'],d['You']
CC1=np.uint64(0x0000000006600000); CORE=np.uint64(0x0000066006600000)
c1m=pc(Me&CC1&(Me>>np.uint64(16))).astype(np.int16)
c1y=pc(You&CC1&(You>>np.uint64(16))).astype(np.int16)
C1=np.stack([c1m,c1y],1)

def bit(a,i): return ((a>>np.uint64(i))&np.uint64(1)).astype(np.int64)
st=np.zeros((n,31),dtype=np.int16)
for (x,y) in [(1,1),(1,2),(2,1),(2,2)]:
    c=x+4*y
    mb=[bit(Me,c+16*z) for z in range(4)]; yb=[bit(You,c+16*z) for z in range(4)]
    h=sum(mb[z]|yb[z] for z in range(4)); val=mb[0]+2*mb[1]+4*mb[2]+8*mb[3]
    st[np.arange(n),(1<<h)-1+(val&((1<<h)-1))]+=1
def sname(idx):
    h=0
    while (1<<(h+1))-1<=idx: h+=1
    val=idx-((1<<h)-1)
    return '空' if h==0 else ''.join('自' if (val>>j)&1 else '敵' for j in range(h))+'.'*(4-h)

def fit(X,pp,iters=30,ridge=1e-4):
    w=np.zeros(X.shape[1])
    for _ in range(iters):
        q=1.0/(1.0+np.exp(-(X@w)/400.0)); g=X.T@(q-pp)/400.0
        H=X.T@(X*(q*(1-q)/160000.0)[:,None])+ridge*np.eye(X.shape[1])
        s=np.linalg.solve(H,g); w-=s
        if np.max(np.abs(s))<1e-9: break
    return w

for s in (0,1):
    for b in (0,1):
        sel=(d['side']==s)&(bucket==b)
        lab=f"{'fir(黒手番)' if s==0 else 'sec(白手番)'} bucket{b} turn{turn[sel].min()}-{turn[sel].max()}"
        X0=d['f'][sel].astype(np.float64); pp=p[sel]
        m,y=c1m[sel],c1y[sel]
        print(f"\n=== {lab}  n={sel.sum()} ===")
        print(f"  自分の核ペア>=1 の局面 {100*(m>=1).mean():.1f}% / 相手 {100*(y>=1).mean():.1f}%  平均本数 自{m.mean():.3f} 敵{y.mean():.3f}")
        w=fit(np.hstack([X0,C1[sel].astype(np.float64)]),pp)
        print(f"  学習された重み: 自分の核ペア {w[-2]:+.0f} / 相手の核ペア {w[-1]:+.0f}")
        print(f"   (参考 既存重み: stdweight[+2]={w[3]:+.0f}, continuous={w[14]:+.0f}, layer_me[3段]={w[5]:+.0f})")
        w2=fit(np.hstack([X0,st[sel][:,1:].astype(np.float64)]),pp)
        tab=[(sname(i),w2[PNUM+i-1],int(st[sel][:,i].sum())) for i in range(1,31)]
        tab=[x for x in tab if x[2]>sel.sum()*0.002]
        tab.sort(key=lambda x:-x[1])
        print("  中心棒パターン表(上位/下位, 自=手番側の石, 左が下段):")
        for nm,v,c in tab[:6]:  print(f"    {nm:<6} {v:+7.0f}  (出現 {c})")
        print("     ...")
        for nm,v,c in tab[-6:]: print(f"    {nm:<6} {v:+7.0f}  (出現 {c})")
