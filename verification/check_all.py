#!/usr/bin/env python3
"""Rebuild and audit all checked Lean modules; optionally run finite experiments."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import re
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
LEAN = ROOT / 'verification/lean'

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packages-dir', type=Path, default=LEAN / '.lake/packages')
    parser.add_argument('--experiments', action='store_true')
    parser.add_argument('--check-record', action='store_true', help='Check recorded hashes without rebuilding Lean')
    args = parser.parse_args()
    if args.check_record:
        path = ROOT / 'verification/last_run.json'
        record = json.loads(path.read_text())
        changed = [name for name, digest in record['sha256'].items()
                   if not (ROOT / name).is_file() or hashlib.sha256((ROOT / name).read_bytes()).hexdigest() != digest]
        if not record.get('success') or changed:
            print('STALE OR FAILED: ' + ', '.join(changed))
            return 1
        print('PASS: successful audit matches the recorded drafts and sources; Lean was not rerun.')
        return 0
    scripts = ['check_fptas_calculations.py', 'check_sampled_markov.py', 'check_line_restriction.py', 'check_scaled_polynomial.py', 'check_cover_arithmetic.py', 'check_cover_assembly.py', 'check_chamber_insertion.py', 'check_cell_encoding.py']
    sources = [LEAN / name for name in ['FPTASCalculations.lean', 'SampledMarkov.lean', 'LineRestriction.lean', 'ScaledPolynomial.lean', 'CoverArithmetic.lean', 'CoverAssembly.lean', 'ChamberInsertion.lean', 'CellEncoding.lean', 'lake-manifest.json', 'lakefile.toml', 'lean-toolchain'] + scripts]
    sources += [Path(__file__).resolve(), ROOT / 'verification/make_review_draft.py',
                ROOT / 'verification/README.md', ROOT / 'verification/reference_audit.txt',
                ROOT / 'README.md', ROOT / 'reflecting_cells_fptas_review.tex']
    # Bind this audit to the exact accompanying drafts, not just Lean sources.
    sources += [ROOT / name for name in ['reflecting_cells_fptas_short.tex', 'reflecting_cells_fptas.tex']]
    if args.experiments:
        sources += [ROOT / 'experiments' / n for n in ['check_reflecting_cells.py', 'check_shifted_chambers.py']]
    record = {'started_utc': datetime.now(timezone.utc).isoformat(), 'success': False,
              'toolchain': (LEAN / 'lean-toolchain').read_text().strip(),
              'sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
              'checks': []}
    output = ROOT / 'verification/last_run.json'
    def save():
        output.write_text(json.dumps(record, indent=2) + '\n')
    save()
    if not shutil.which('elan'):
        print('Missing elan: install elan and add its bin directory to PATH.', file=sys.stderr)
        return 1
    packages = args.packages_dir.resolve()
    manifest = json.loads((LEAN / 'lake-manifest.json').read_text())
    missing = [p['name'] for p in manifest['packages'] if not (packages / p['name']).is_dir()]
    if missing:
        print('Missing dependencies: ' + ', '.join(missing) + '. Run lake exe cache get in verification/lean.', file=sys.stderr)
        return 1
    commands = [[sys.executable, str(LEAN / s), '--packages-dir', str(packages)] for s in scripts]
    if args.experiments:
        commands += [[sys.executable, str(ROOT / 'experiments' / n)] for n in ['check_reflecting_cells.py', 'check_shifted_chambers.py']]
    for command in commands:
        print('\nChecking ' + Path(command[1]).name, flush=True)
        result = subprocess.run(command, cwd=ROOT)
        record['checks'].append({'script': str(Path(command[1]).relative_to(ROOT)), 'exit_code': result.returncode})
        save()
        if result.returncode:
            print('FAILED; see output above. Aggregate success is false.', file=sys.stderr)
            return 1
    record.update(success=True, finished_utc=datetime.now(timezone.utc).isoformat())
    save()
    count = sum(len(re.findall(r'^theorem \w+', (LEAN / name).read_text(), re.M)) for name in ['FPTASCalculations.lean', 'SampledMarkov.lean', 'LineRestriction.lean', 'ScaledPolynomial.lean', 'CoverArithmetic.lean', 'CoverAssembly.lean', 'ChamberInsertion.lean', 'CellEncoding.lean'])
    print(f'\nPASS: all eight Lean modules rebuilt and axiom-audited ({count} theorems).')
    print('Run record: ' + str(output))
    return 0

if __name__ == '__main__':
    sys.exit(main())
