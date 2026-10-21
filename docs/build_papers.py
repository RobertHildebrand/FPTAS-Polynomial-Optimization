"""Build the guide's PDF links from the current standalone manuscript sources."""
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import tempfile

root = Path(__file__).resolve().parent.parent
out = root / 'docs/papers'
out.mkdir(exist_ok=True)
manifest = {}
for stem in ['reflecting_cells_fptas_short', 'reflecting_cells_fptas', 'reflecting_cells_fptas_review']:
    source = root / (stem + '.tex')
    with tempfile.TemporaryDirectory(prefix='fptas-pdf-') as build:
        for _ in range(2):
            run = subprocess.run(['pdflatex', '-interaction=nonstopmode', '-halt-on-error',
                                  '-output-directory=' + build, str(source)], cwd=root,
                                 stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, errors='replace')
            if run.returncode:
                raise SystemExit(run.stdout)
        shutil.copy2(Path(build) / (stem + '.pdf'), out / (stem + '.pdf'))
    manifest[stem] = {'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
                      'pdf_sha256': hashlib.sha256((out / (stem + '.pdf')).read_bytes()).hexdigest()}
    print('Built ' + stem + '.pdf')
(out / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
