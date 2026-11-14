# -*- coding: utf-8 -*-
"""調査その3: 現行 ver8_2 の重み(既存GDの解)と、同じ29特徴を素直にニュートン法で
             解き直した解の loss を比べる。= 最適化器の取りこぼしを測る。"""
import numpy as np, re
PNUM=29
DT = np.dtype([('Me','<u8'),('You','<u8'),('game','<i4'),('teacher','<i4'),
               ('ply','<i2'),('result','i1'),('side','i1'),('f','<i2',(PNUM,))])
d = np.fromfile('out/probe_ver8_2.bin', dtype=DT)
turn = d['ply'].astype(np.int32)+2
bucket = np.where(d['side']==0,(turn-4)//14,(turn-5)//14)
t=d['teacher'].astype(np.float64)
with np.errstate(over='ignore'):
    p=np.where(t<-1840,0.99,np.where(t>1840,0.01,1.0-1.0/(1.0+np.exp(-t/400.0))))

# weights/alpha/ver8_2.txt を読む
W={}
side=None;b=None
for line in open('../../weights/alpha/ver8_2.txt', encoding='utf-8'):
    line=line.split('#')[0].strip()
    if not line: continue
    m=re.match(r'\[(fir|sec)\.bucket(\d)\]',line)
    if m: side,b=m.group(1),int(m.group(2)); continue
    if '=' in line:
        k,v=line.split('=',1)
        W[(side,b,k.strip())]=[int(x) for x in v.split(',')]
def ps_of(side,b):
    sw=W[(side,b,'stdweight')]; mk=W[(side,b,'maketweight')]; cm=W[(side,b,'conti_maketweight')]
    lm=W[(side,b,'layer_me')]; ly=W[(side,b,'layer_you')]; it=W[(side,b,'intersection')]
    co=W[(side,b,'continuous')]
    return np.array([sw[1],sw[2],sw[4],sw[5]]+lm+ly+it+co+mk[0:4]+mk[4:8]+cm[0:3]+cm[3:6],dtype=np.float64)

def fit(X,p,iters=30,ridge=1e-6):
    w=np.zeros(X.shape[1])
    for _ in range(iters):
        q=1.0/(1.0+np.exp(-(X@w)/400.0))
        g=X.T@(q-p)/400.0
        H=X.T@(X*(q*(1-q)/160000.0)[:,None])+ridge*np.eye(X.shape[1])
        st=np.linalg.solve(H,g); w-=st
        if np.max(np.abs(st))<1e-9: break
    return w
def loss(X,w,p):
    q=np.clip(1.0/(1.0+np.exp(-(X@w)/400.0)),1e-12,1-1e-12)
    return float((-p*np.log(q)-(1-p)*np.log1p(-q)).sum())

print('  side/bucket   ver8_2重み      ニュートン法(同じ29特徴)   差')
for s in (0,1):
    for b in (0,1,2,3):
        sel=(d['side']==s)&(bucket==b)
        if sel.sum()==0: continue
        X=d['f'][sel].astype(np.float64); pp=p[sel]; g=d['game'][sel]
        tr=(g%2==1); te=~tr
        w_cur=ps_of('fir' if s==0 else 'sec', b)
        l_cur=loss(X[te],w_cur,pp[te])/te.sum()
        w_new=fit(X[tr],pp[tr]); l_new=loss(X[te],w_new,pp[te])/te.sum()
        print(f"  {'fir' if s==0 else 'sec'} b{b}  n={sel.sum():7d}  {l_cur:.6f}   {l_new:.6f}   {l_new-l_cur:+.6f}")
        if b==0 and s==0:
            print('   ver8_2 :', w_cur.astype(int))
            print('   newton :', w_new.round(0).astype(int))
