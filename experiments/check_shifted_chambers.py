"""Exact 2D regression checks for the shifted closed-chamber construction.

Uses rational polygon clipping and exhaustive lattice enumeration, not an IP
oracle or the claimed running-time algorithm. Checks original boundary points,
a lower-dimensional original polytope, and an integer-infeasible instance.
"""
from fractions import Fraction as F
from itertools import product
from math import ceil, floor, comb
from pathlib import Path
import json


def dot(a, x):
    return sum(u*v for u, v in zip(a, x))


def clip(poly, a, b):
    out = []
    for x, y in zip(poly, poly[1:]+poly[:1]):
        sx, sy = b-dot(a,x), b-dot(a,y)
        if sx >= 0:
            out.append(x)
        if (sx < 0 < sy) or (sy < 0 < sx):
            t = sx/(sx-sy)
            out.append(tuple(u+t*(v-u) for u,v in zip(x,y)))
    # Drop repeated consecutive vertices, including the closing pair.
    clean = []
    for x in out:
        if not clean or x != clean[-1]:
            clean.append(x)
    if len(clean)>1 and clean[0]==clean[-1]:
        clean.pop()
    if len(clean)<3:
        return []
    area = sum(x[0]*y[1]-x[1]*y[0] for x,y in zip(clean,clean[1:]+clean[:1]))
    return clean if area else []


def contains(poly, x):
    return all((y[0]-u[0])*(x[1]-u[1])-(y[1]-u[1])*(x[0]-u[0]) >= 0
               for u,y in zip(poly,poly[1:]+poly[:1]))


def run(name, bounds, extra=()):
    A=[(1,0),(-1,0),(0,1),(0,-1)]
    b=[bounds[0][1],-bounds[0][0],bounds[1][1],-bounds[1][0]]
    for a,rhs in extra:
        A.append(a);b.append(rhs)
    tau=(1+max(abs(z) for row in A for z in row)+max(abs(z) for z in b)).bit_length()
    # A conservative instance of the paper's explicit Schrijver exponent.
    Phi=4*4*3*(tau+3)+tau+2+2
    ell=4; D=2; eps=F(1,4)
    cuts=sorted({F(2)**Phi}|{F(2)**k*(1+F(j,ell)) for k in range(-2,Phi) for j in range(ell)})
    left,right=F(bounds[0][0])-F(1,4),F(bounds[0][1])+F(1,4)
    low,high=F(bounds[1][0])-F(1,4),F(bounds[1][1])+F(1,4)
    Q=[(left,low),(right,low),(right,high),(left,high)]
    for a,rhs in zip(A,b):
        Q=clip(Q,a,F(rhs)+F(1,4)) if Q else []
        Q=clip(Q,tuple(-z for z in a),F(2)**Phi-F(rhs)-F(1,2)) if Q else []
    cells=[Q] if Q else []
    planes=0
    for a,rhs in zip(A,b):
        if not Q: break
        lo=min(F(rhs)+F(1,2)-dot(a,x) for x in Q)
        hi=max(F(rhs)+F(1,2)-dot(a,x) for x in Q)
        for t in cuts:
            if not lo<t<hi: continue
            planes+=1
            bound=F(rhs)+F(1,2)-t
            new=[]
            for C in cells:
                for normal,r in [(a,bound),(tuple(-z for z in a),-bound)]:
                    child=clip(C,normal,r)
                    if child: new.append(child)
            cells=new
    assert len(cells)<=sum(comb(planes,j) for j in range(3) if j<=planes)
    lattice=list(product(*(range(ceil(lo),floor(hi)+1) for lo,hi in [(left,right),(low,high)])))
    feasible={x for x in lattice if all(dot(a,x)<=rhs for a,rhs in zip(A,b))}
    covered=set();reps=[];memberships=0;nontrivial_pairs=0
    for C in cells:
        # Weak interval width is checked from exact vertex extrema for EVERY row.
        for a,rhs in zip(A,b):
            vals=[F(rhs)+F(1,2)-dot(a,x) for x in C]
            assert ell*(max(vals)-min(vals))<=min(vals)
        local_points=product(*(range(ceil(min(x[j] for x in C)),floor(max(x[j] for x in C))+1) for j in range(2)))
        points=[x for x in local_points if contains(C,x)]
        assert set(points)<=feasible
        covered.update(points);memberships+=len(points)
        if not points: continue
        reps.append(points[0])
        # Endpoint tests suffice for linear slacks along each entire progression.
        for x,y in product(points,repeat=2):
            nontrivial_pairs += x != y
            for k in [-ell,ell]:
                z=tuple(u+k*(v-u) for u,v in zip(x,y))
                assert all(dot(a,z)<=rhs for a,rhs in zip(A,b))
    assert covered==feasible
    objectives=[lambda x:x[0]**2-x[1]**2+3*x[0]*x[1],
                lambda x:(x[0]-1)**2+(x[1]+1)**2]
    if feasible:
        for f in objectives:
            mn,mx=min(map(f,feasible)),max(map(f,feasible))
            assert min(map(f,reps))-mn<=eps*(mx-mn)
            assert mx-max(map(f,reps))<=eps*(mx-mn)
    else:
        assert not reps
    return dict(name=name,cells=len(cells),integer_points=len(feasible),
                memberships=memberships,representatives=len(reps),nontrivial_pairs=nontrivial_pairs,passed=True)


def main():
    results=[run('unit square: boundary integer points',((0,1),(0,1))),
             run('pentagon: nonconvex quadratic',((0,3),(0,3)),[((1,1),4)]),
             run('wide square: nontrivial progressions',((-16,16),(-16,16))),
             run('lower-dimensional original segment',((0,3),(0,0))),
             run('real feasible, integer infeasible',((0,1),(0,1)),[((3,0),2),((-3,0),-1)])]
    target=Path(__file__).with_name('shifted_chambers_results.json')
    target.write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(results,indent=2))
    print('PASS: exact shifted chambers, coverage, original feasibility, progressions and error checks.')

if __name__=='__main__':main()
