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
    args = parser.parse_args()
    scripts = ['check_fptas_calculations.py', 'check_sampled_markov.py', 'check_line_restriction.py']
    sources = [LEAN / name for name in ['FPTASCalculations.lean', 'SampledMarkov.lean', 'LineRestriction.lean', 'lake-manifest.json', 'lakefile.toml', 'lean-toolchain'] + scripts]
    sources += [Path(__file__).resolve()]
    if args.experiments:
        sources.append(ROOT / 'experiments/check_reflecting_cells.py')
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
        commands.append([sys.executable, str(ROOT / 'experiments/check_reflecting_cells.py')])
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
    count = sum(len(re.findall(r'^theorem \w+', (LEAN / name).read_text(), re.M)) for name in ['FPTASCalculations.lean', 'SampledMarkov.lean', 'LineRestriction.lean'])
    print(f'\nPASS: all three Lean modules rebuilt and axiom-audited ({count} theorems).')
    print('Run record: ' + str(output))
    return 0

if __name__ == '__main__':
    sys.exit(main())
