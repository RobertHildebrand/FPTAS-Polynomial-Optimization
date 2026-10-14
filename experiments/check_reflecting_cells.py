"""Exact small-instance reference implementation, not an efficient FPTAS.

Enumerates a supplied bounding box, groups feasible lattice points by their
exact arrangement face, and implements each cell's feasibility oracle by lookup.
This deliberately avoids trusting an external IP solver. It checks the actual
refined thresholds, including singleton faces, against exhaustive optima.
Run with Python 3; no dependencies. Lean is not involved.
"""
from bisect import bisect_left
from fractions import Fraction
from itertools import product
from math import isqrt
from random import Random
from pathlib import Path
import json


def ceil_log2(n):
    return (n - 1).bit_length()


def refinement(degree, epsilon):
    n = degree ** 4 * epsilon.denominator
    ell = isqrt(n // epsilon.numerator)
    return ell if ell * ell * epsilon.numerator >= n else ell + 1


def thresholds(M, ell):
    return sorted({Fraction(0), Fraction(2 ** M)} |
                  {Fraction((2 ** k) * (ell + j), ell)
                   for k in range(M) for j in range(ell)})


def face(slack, cuts):
    j = bisect_left(cuts, slack)
    return ('eq', j) if cuts[j] == slack else ('open', j - 1)


def slacks(point, A, b):
    return tuple(rhs - sum(a * x for a, x in zip(row, point))
                 for row, rhs in zip(A, b))


def evaluate(terms, point):
    total = 0
    for coefficient, exponents in terms:
        value = coefficient
        for x, exponent in zip(point, exponents):
            value *= x ** exponent
        total += value
    return total


def box_system(bounds):
    d = len(bounds)
    A, b = [], []
    for j, (lo, hi) in enumerate(bounds):
        row = [0] * d
        row[j] = 1
        A.extend([row, [-v for v in row]])
        b.extend([hi, -lo])
    return A, b


def run_case(name, bounds, objectives, degree, epsilon, extra=()):
    A, b = box_system(bounds)
    for row, rhs in extra:
        A.append(row)
        b.append(rhs)
    d = len(bounds)
    tau = ceil_log2(2 + max(abs(v) for row in A for v in row))
    tau = max(tau, ceil_log2(2 + max(map(abs, b))))
    V = d * (tau + ceil_log2(d + 1)) + 2
    M = tau + V + ceil_log2(d + 1) + 2
    ell = refinement(degree, epsilon)
    cuts = thresholds(M, ell)
    groups = {}
    for x in product(*(range(lo, hi + 1) for lo, hi in bounds)):
        sx = slacks(x, A, b)
        if min(sx) < 0:
            continue
        assert max(sx) < 2 ** M
        key = tuple(face(v, cuts) for v in sx)
        groups.setdefault(key, []).append(x)
    # Validate the full cell extrapolation algebra, including noninteger points.
    for key in groups:
        for kind, j in key:
            if kind == 'eq':
                continue
            low, high = cuts[j:j + 2]
            assert low >= 1  # no integer point can lie in (0,1)
            assert ell * (high - low) <= low
    # Independently verify every same-cell pair's progression feasibility using
    # extreme integer slack values: min(s)-ell*(max(s)-min(s)) >= 0.
    for points in groups.values():
        values = [slacks(x, A, b) for x in points]
        for column in zip(*values):
            assert min(column) - ell * (max(column) - min(column)) >= 0
    results = []
    for label, terms in objectives:
        assert all(sum(e) <= degree for _, e in terms)
        if not groups:
            results.append({'objective': label, 'status': 'INFEASIBLE'})
            continue
        vals = {x: evaluate(terms, x) for points in groups.values() for x in points}
        lo, hi = min(vals.values()), max(vals.values())
        R = hi - lo
        budget = epsilon * R
        lemma_budget = Fraction(degree ** 4, ell ** 2) * R
        reps = [points[0] for points in groups.values()]
        approx_min, approx_max = min(vals[x] for x in reps), max(vals[x] for x in reps)
        assert approx_min - lo <= budget
        assert hi - approx_max <= budget
        # Stronger than trying random representatives: let an adversary choose
        # the WORST representative separately in every cell for minimization.
        worst_min = min(max(vals[x] for x in points) for points in groups.values())
        worst_max = max(min(vals[x] for x in points) for points in groups.values())
        assert worst_min - lo <= budget
        assert hi - worst_max <= budget
        checks = 0
        for points in groups.values():
            cell_lo, cell_hi = min(vals[x] for x in points), max(vals[x] for x in points)
            if cell_lo == lo or cell_hi == hi:
                assert cell_hi - cell_lo <= lemma_budget
                # Explicitly check the polynomial on the full progression to
                # the worst representative of each extremum-containing cell.
                for sign, optimum in [(1, lo), (-1, hi)]:
                    if not any(vals[x] == optimum for x in points):
                        continue
                    x = next(x for x in points if vals[x] == optimum)
                    y = max(points, key=lambda z: sign * vals[z])
                    samples = []
                    for k in range(-ell, ell + 1):
                        z = tuple(u + k * (v - u) for u, v in zip(x, y))
                        assert min(slacks(z, A, b)) >= 0
                        value = evaluate(terms, z)
                        assert lo <= value <= hi
                        samples.append(sign * value)
                    assert samples[ell - 1] >= samples[ell]
                    assert samples[ell + 1] - samples[ell] <= lemma_budget
                    checks += 1
        results.append({'objective': label, 'minimum': lo, 'maximum': hi,
                        'returned_minimum': approx_min,
                        'adversarial_minimum': worst_min,
                        'worst_relative_error': str(Fraction(max(worst_min-lo, hi-worst_max), R)) if R else '0',
                        'progressions_checked': checks})
    return {'case': name, 'degree': degree, 'epsilon': str(epsilon), 'ell': ell,
            'lattice_points': sum(map(len, groups.values())), 'occupied_cells': len(groups),
            'largest_cell': max(map(len, groups.values()), default=0), 'results': results}


def random_objectives(d, degree, count, rng):
    exps = [e for e in product(range(degree + 1), repeat=d) if sum(e) <= degree]
    return [('random_%d' % j, [(rng.randint(-7, 7), e) for e in exps])
            for j in range(count)]


def negative_control():
    # Omit the required refinement: the best of adversarial representatives
    # must now FAIL the requested 0.1% range-relative guarantee.
    cuts = thresholds(12, 1)
    cells = {}
    for x in range(-1000, 1001):
        key = (face(1000+x, cuts), face(1000-x, cuts))
        cells.setdefault(key, []).append((x-123)**2)
    worst_answer = min(max(values) for values in cells.values())
    relative_error = Fraction(worst_answer, 1123**2)
    assert relative_error > Fraction(1, 1000)
    return {'purpose': 'detect omitted refinement', 'ell': 1,
            'requested_epsilon': '1/1000', 'adversarial_relative_error': str(relative_error),
            'expected_guarantee_failure_detected': True}


def main():
    rng = Random(20261013)
    reports = []
    # Shifted interior minima deliberately avoid threshold singleton faces.
    for degree in [2, 3, 4, 6]:
        terms = [(1, (2,)), (-246, (1,)), (15129, (0,))]
        objectives = [('shifted_square', terms)] + random_objectives(1, degree, 8, rng)
        if degree >= 4:
            objectives += [('double_well', [(1,(4,)),(-492,(3,)),(90766,(2,)),(-7441500,(1,)),((123**2-4)**2,(0,))])]
        for eps in [Fraction(1, 2), Fraction(1, 10)]:
            reports.append(run_case('interval_D%d' % degree, [(-1000,1000)], objectives, degree, eps))
    quartic = [(1,(4,0)),(-2,(2,0)),(2,(0,0)),(1,(0,2)),(1,(0,1))]
    shifted = [(1,(2,0)),(-26,(1,0)),(169,(0,0)),(1,(0,2)),(-34,(0,1)),(289,(0,0))]
    objectives = [('nonconvex_quartic', quartic), ('interior_square', shifted)] + random_objectives(2,4,8,rng)
    for eps in [Fraction(1,2), Fraction(1,10)]:
        reports.append(run_case('box', [(-80,80)]*2, objectives,4,eps))
        reports.append(run_case('oblique', [(-80,80)]*2, objectives,4,eps,
                                [([2,3],160),([-3,1],110)]))
    reports.append(run_case('lower_dimensional', [(-100,100)]*2, objectives,4,Fraction(1,2),
                            [([1,-1],0),([-1,1],0)]))
    reports.append(run_case('empty_integer_set', [(0,2)], [('linear',[(1,(1,))])],1,Fraction(1,2),
                            [([2],1),([-2],-1)]))
    reports.append(run_case('constant_and_affine', [(-80,80)]*2,
                            [('constant',[(7,(0,0))]),('affine',[(3,(1,0)),(-2,(0,1))])],1,Fraction(1,2)))
    # A large binary coefficient and large translated coordinates.
    B = 10**30
    reports.append(run_case('large_encoding', [(B-1000,B+1000)],
                            [('translated_square',[(1,(2,)),(-2*(B+123),(1,)),((B+123)**2,(0,))])],
                            2,Fraction(1,10)))
    output = Path(__file__).with_name('results.json')
    control = negative_control()
    output.write_text(json.dumps({'cases': reports, 'negative_control': control}, indent=2)+'\n')
    count = sum(len(r['results']) for r in reports)
    print('PASS:',len(reports),'geometries/accuracy settings;',count,'objective tests')
    for r in reports:
        errors = [Fraction(v['worst_relative_error']) for v in r['results'] if 'worst_relative_error' in v]
        print(r['case'], 'eps='+r['epsilon'], 'points='+str(r['lattice_points']),
              'cells='+str(r['occupied_cells']), 'max_cell='+str(r['largest_cell']),
              'worst_error='+str(max(errors, default=Fraction(0))))
    print('PASS: negative control detects failure without refinement:', control['adversarial_relative_error'])
    print('Exact results:', output)


if __name__ == '__main__':
    main()
