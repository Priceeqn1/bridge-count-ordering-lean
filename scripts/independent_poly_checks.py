#!/usr/bin/env python3
"""Exact, independent finite-endpoint checks for the proposed Lean theorem.

Not a formal certificate: enumerate all increasing paths, compute joint count
arrays with polynomial monomials in independently indexed site activities,
and inspect every coefficient of every ordered minor.
"""
from collections import defaultdict
from itertools import combinations
from math import comb
from pathlib import Path
import json


def polynomial_product(p, q):
    out=defaultdict(int)
    for a, ca in p.items():
        for b, cb in q.items():
            out[tuple(x+y for x,y in zip(a,b))]+=ca*cb
    return {mon:c for mon,c in out.items() if c}


def minor(p, q, r, s):
    xy=polynomial_product(p,s)
    zw=polynomial_product(q,r)
    out=defaultdict(int,xy)
    for mon,c in zw.items(): out[mon]-=c
    return {mon:c for mon,c in out.items() if c}


def kernel(k, kind):
    K=[[0]*(k+1) for _ in range(k+1)]
    for n in range(1,k+1):
        for j in range(n):
            if kind=='Pascal': K[n][j]=comb(n,j)
            elif kind=='Power': K[n][j]=2**(n*j)
            elif kind=='Flat': K[n][j]=1
            elif kind=='Positive-column-only': K[n][j]=100 if (n,j)==(3,0) else 1
            elif kind=='Ktheta100': K[n][j]=100 if (n,j)==(3,1) else 1
            else: raise ValueError(kind)
    return K


def tp2_violations(K, positive_only=False):
    k=len(K)-1
    return [(u,v,i,j) for u in range(k+1) for v in range(u+1,k+1)
        for i in range(1 if positive_only else 0,k+1) for j in range(i+1,k+1)
        if K[u][i]*K[v][j] < K[u][j]*K[v][i]]


def count_array(k,K,q,suffix):
    # Rows are r=0,...,k-1 (number of internal vertices),
    # columns s=0,...,k-1 (number of visits to the chosen interval).
    A={}
    for r in range(k):
        for subset in combinations(range(1,k),r):
            vertices=(0,)+subset+(k,)
            w=1
            for j,n in zip(vertices[:-1],vertices[1:]):
                w*=K[n][j]
            s=sum((j>=q) if suffix else (j<=q) for j in subset)
            mon=[0]*(k+1)
            for j in subset: mon[j]+=1
            P=A.setdefault((r,s),defaultdict(int))
            P[tuple(mon)]+=w
    return A


def all_minors(A,k):
    bad=[]
    count=0
    for r in range(k):
        for rr in range(r+1,k):
            for s in range(k):
                for ss in range(s+1,k):
                    p=A.get((r,s),{})
                    q=A.get((r,ss),{})
                    v=A.get((rr,s),{})
                    w=A.get((rr,ss),{})
                    M=minor(p,q,v,w)
                    count+=1
                    neg={mon:c for mon,c in M.items() if c<0}
                    if neg: bad.append({'indices':[r,rr,s,ss], 'negative_count':len(neg), 'sample_coeff':next(iter(neg.values()))})
    return count,bad


def run():
    results=[]
    for k in range(4,8):
      for kind in ['Pascal','Power','Flat','Positive-column-only','Ktheta100']:
        K=kernel(k,kind)
        full=not tp2_violations(K)
        positive=not tp2_violations(K,True)
        for suffix in [False,True]:
          total=0
          failures=0
          witness=None
          for q in range(1,k):
            count,bad=all_minors(count_array(k,K,q,suffix),k)
            total+=count
            failures+=len(bad)
            if bad and witness is None:
                witness={'q':q,**bad[0]}
          results.append({'k':k,'kernel':kind,'full_tp2':full,
                          'positive_column_tp2':positive,
                          'interval':'suffix' if suffix else 'prefix',
                          'tested_minors':total,'negative_minors':failures,
                          'first_failure':witness})
          if (full or (positive and not suffix)) and failures:
             raise AssertionError(('Theorem finite counterexample',results[-1]))
    # Ensure a nontrivial counterexample for suffix with only positive-column TP2
    assert any(x['kernel']=='Positive-column-only' and x['interval']=='suffix' and x['negative_minors']>0 for x in results)
    assert any(x['kernel']=='Ktheta100' and x['interval']=='suffix' and x['negative_minors']>0 for x in results)
    root=Path(__file__).resolve().parents[1]
    summary={'total_cases':len(results),'tested_minors':sum(x['tested_minors'] for x in results),
             'theorem_matching_failures':0,
             'deliberate_negative_control_failures':sum(x['negative_minors'] for x in results if x['interval']=='suffix' and not x['full_tp2']),
             'results':results}
    (root/'finite_check_report.json').write_text(json.dumps(summary,indent=2))
    print(json.dumps({k:v for k,v in summary.items() if k!='results'},indent=2))
    for x in results:
      if x['first_failure']:
        print(f"Negative-control witness: k={x['k']} kernel={x['kernel']} cut={x['interval']} q={x['first_failure']['q']} indices={x['first_failure']['indices']} coefficient={x['first_failure']['sample_coeff']}")

if __name__=='__main__': run()
