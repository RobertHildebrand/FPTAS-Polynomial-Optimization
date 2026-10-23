"""Build an arXiv copy with extra room for the first-page margin stamp."""
from pathlib import Path
import hashlib,json,shutil,subprocess,tempfile,zipfile
root=Path(__file__).resolve().parent.parent
out=root/'submission'
source=(root/'reflecting_cells_fptas_short.tex').read_text()
# Preserve text width, line breaks, and page count; shift the block 20pt right.
adjustment='''% arXiv copy: reserve additional left-margin space for arXiv's stamp.
\\addtolength{\\oddsidemargin}{20pt}
\\addtolength{\\evensidemargin}{20pt}
'''
source=source.replace('\\begin{document}',adjustment+'\\begin{document}',1)
with tempfile.TemporaryDirectory(prefix='fptas-arxiv-') as tmp:
 d=Path(tmp);tex=d/'reflecting_cells_fptas_short.tex';tex.write_text(source)
 for _ in range(2):
  run=subprocess.run(['pdflatex','-interaction=nonstopmode','-halt-on-error',tex.name],cwd=d,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,errors='replace')
  if run.returncode:raise RuntimeError(run.stdout)
 shutil.copy2(d/'reflecting_cells_fptas_short.pdf',out/'manuscript_arxiv.pdf')
 with zipfile.ZipFile(out/'arxiv_source.zip','w',zipfile.ZIP_DEFLATED) as z:
  z.write(tex,tex.name)
  z.write(out/'verification_supplement.pdf','anc/verification_supplement.pdf')
print('Built arxiv_source.zip and manuscript_arxiv.pdf; journal layout unchanged.')
j=json.loads((out/'manifest.json').read_text());j['arxiv_source_sha256']=hashlib.sha256(source.encode()).hexdigest();j['arxiv_layout']='Journal text width preserved; text block shifted 20pt right for arXiv stamp.';(out/'manifest.json').write_text(json.dumps(j,indent=2)+'\n')
with zipfile.ZipFile(root/'submission_materials.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in sorted(out.iterdir()):
  if p.is_file():z.write(p,'submission/'+p.name)
