"""Compile the FPTAS algebraic calculations and audit every theorem's axioms.
Use --packages-dir to reuse a compiled tree matching lake-manifest.json.
"""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess

root = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--packages-dir', type=Path, default=root / '.lake/packages')
args = parser.parse_args()
manifest = json.loads((root / 'lake-manifest.json').read_text())
packages = args.packages_dir.resolve()
for p in manifest['packages']:
    revision = subprocess.check_output(['git', '-C', str(packages/p['name']), 'rev-parse', 'HEAD'], text=True).strip()
    if revision != p['rev']:
        raise SystemExit('Dependency revision mismatch: ' + p['name'])
build = root / '.lake/build/lib/lean'
build.mkdir(parents=True, exist_ok=True)
env = os.environ.copy()
env['LEAN_PATH'] = os.pathsep.join([str(build)] + [str(packages/p['name']/'.lake/build/lib/lean') for p in manifest['packages']])
base = ['elan', 'run', (root/'lean-toolchain').read_text().strip(), 'lean']
source = (root/'CellEncoding.lean').read_text()
names = re.findall(r'^theorem (\w+)', source, re.M)
audit = root / '.lake/CellEncodingAudit.lean'
audit.write_text('import CellEncoding\n' + '\n'.join('#print axioms CellEncoding.' + n for n in names) + '\n')
log = [subprocess.check_output(base + ['--version'], text=True).strip(), 'Mathlib: ' + manifest['packages'][0]['rev']]
modules = ['FPTASCalculations', 'SampledMarkov', 'LineRestriction', 'ScaledPolynomial', 'CoverArithmetic', 'CoverAssembly', 'ChamberInsertion', 'CellEncoding']
commands = [base + ['-o', str(build/(name+'.olean')), name+'.lean'] for name in modules]
for command in commands + [base + [str(audit)]]:
    result = subprocess.run(command, cwd=root, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print(result.stdout, flush=True)
    log.append(result.stdout)
    if result.returncode or 'sorryAx' in result.stdout or re.search(r"uses .sorry.", result.stdout):
        raise SystemExit('Verification failed')
reports = re.findall(r'depends on axioms: \[([^\]]*)\]|does not depend on any axioms', log[-1])
if len(reports) != len(names):
    raise SystemExit('Missing axiom report')
for report in reports:
    if set(filter(None, (s.strip() for s in report.split(',')))) - {'propext', 'Classical.choice', 'Quot.sound'}:
        raise SystemExit('Unexpected axiom: ' + report)
log.append(f'PASS: {len(names)} theorems; no custom axioms or sorryAx.')
(root/'cell_encoding_verification_log.txt').write_text('\n'.join(log) + '\n')
print(log[-1])
