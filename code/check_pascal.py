#!/usr/bin/env python3
"""Numerical sanity check for the Lean statements (exact rational arithmetic).

Checks, for random rational points on random conics:
  (1) pascal(A..F) = det[(A×B)×(D×E), (B×C)×(E×F), (C×D)×(F×A)] == 0
  (2) the polynomial identity pascal(v) == -det(Veronese 6x6 matrix) for arbitrary v
      (Veronese row: x², y², z², xy, yz, zx)
  (3) the parametric identity on the standard conic xz = y² with points (s², st, t²).
"""
from fractions import Fraction as Fr
import random

def cross(a, b):
    return (a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0])

def dot(a, b):
    return sum(x*y for x, y in zip(a, b))

def det3(a, b, c):
    return dot(a, cross(b, c))

def det(m):
    m = [row[:] for row in m]; n = len(m); d = Fr(1)
    for i in range(n):
        p = next((r for r in range(i, n) if m[r][i] != 0), None)
        if p is None: return Fr(0)
        if p != i: m[i], m[p] = m[p], m[i]; d = -d
        d *= m[i][i]
        for r in range(i+1, n):
            f = m[r][i] / m[i][i]
            for c in range(i, n): m[r][c] -= f*m[i][c]
    return d

def pascal(A, B, C, D, E, F):
    P = cross(cross(A, B), cross(D, E))
    Q = cross(cross(B, C), cross(E, F))
    R = cross(cross(C, D), cross(F, A))
    return det3(P, Q, R)

def veronese(v):
    x, y, z = v
    return [x*x, y*y, z*z, x*y, y*z, z*x]

def rnd(k=20): return Fr(random.randint(-k, k), random.randint(1, k))

def random_conic_through(p0):
    # random symmetric M with p0ᵀ M p0 = 0: random M, then fix the (0,0) entry
    while True:
        M = [[rnd() for _ in range(3)] for _ in range(3)]
        M = [[(M[i][j]+M[j][i])/2 for j in range(3)] for i in range(3)]
        if p0[0] != 0:
            q = sum(p0[i]*M[i][j]*p0[j] for i in range(3) for j in range(3))
            M[0][0] -= q / (p0[0]*p0[0])
            return M

def Q(M, v): return sum(v[i]*M[i][j]*v[j] for i in range(3) for j in range(3))

def second_point(M, p0, d):
    # points p0 + λ d; Q(p0 + λ d) = 2λ B(p0,d) + λ² Q(d) (since Q(p0)=0); λ = -2B/Q(d)
    Bpd = sum(p0[i]*M[i][j]*d[j] for i in range(3) for j in range(3))
    qd = Q(M, d)
    if qd == 0: return None
    lam = -2*Bpd/qd
    return tuple(p0[i] + lam*d[i] for i in range(3))

random.seed(2026)
N = 300
for trial in range(N):
    p0 = (Fr(random.randint(1, 9)), rnd(), rnd())
    M = random_conic_through(p0)
    pts = [p0]
    while len(pts) < 6:
        p = second_point(M, p0, (rnd(), rnd(), rnd()))
        if p is not None: pts.append(p)
    random.shuffle(pts)
    for p in pts: assert Q(M, p) == 0
    assert pascal(*pts) == 0, "Pascal failed on conic"
    # a non-conic control: perturb one point -> generically nonzero
    bad = list(pts); bad[0] = (bad[0][0]+1, bad[0][1], bad[0][2])
    if trial < 5: print("control (perturbed, expect != 0):", pascal(*bad) != 0)
    # identity with Veronese det for arbitrary points
    vs = [(rnd(), rnd(), rnd()) for _ in range(6)]
    assert pascal(*vs) == -det([veronese(v) for v in vs])
    # parametric
    st = [(rnd(), rnd()) for _ in range(6)]
    assert pascal(*[(s*s, s*t, t*t) for s, t in st]) == 0
    # degenerate conic: pair of lines
    l1, l2 = (rnd(), rnd(), rnd()), (rnd(), rnd(), rnd())
    ps = []
    for i in range(6):
        l = l1 if i % 2 == 0 else l2
        u = (rnd(), rnd(), rnd()); ps.append(cross(l, u))  # point on line l
    assert pascal(*ps) == 0  # Pappus as degenerate Pascal
print(f"OK: {N} trials (conic, Veronese identity, parametric, line-pair/Pappus)")
