# Interactive field guide

Open **index.html** in a modern browser. Keep `style.css`, `geometry.js`, and `explorer.js` beside it. Everything runs offline; there are no external fonts, libraries, analytics, network requests, or build tools.

The guide has two interactive views:

- **Pentagonal cells:** change the refinement, choose an objective, inspect slack intervals, and compare representatives against the exhaustive optimum. Keyboard users can choose an inspection point from the disclosure under the controls.
- **Symmetrization:** vary a cubic's odd coefficient and the integer progression length; the even part stays quadratic.

The instance is `0 <= x,y <= 16`, `x+y <= 24`. It has 253 feasible lattice points. Thresholds follow the manuscript with Phi=5, which suffices for this specific example. The displayed cell count is the number of occupied groups after deterministic boundary assignment, not the total number of chambers. Some closed cells overlap. The demo does not implement the paper's chamber enumerator or integer-feasibility oracle.

The page distinguishes exploratory refinements from those satisfying `ell >= D^2` and `D^2/ell^2 <= epsilon`. Its geometry uses floating-point arithmetic; the exact rational experiments in `../experiments/` provide separate finite-instance checks. Neither demo is a formal proof.

## Test

With Node.js installed, from the repository root:

```sh
node --test docs/explorer.test.js
```

Tests check threshold widths, lattice coverage, the integer progression property, and approximation on the sample objectives. They also check local links and the stated Lean theorem count. No package installation is needed.

To preview over local HTTP instead of opening the file directly:

```sh
python3 -m http.server 8000 --bind 127.0.0.1
```

Visit `http://127.0.0.1:8000/docs/`. Serve the repository root so the paper and verification links resolve. This command does not publish the site. GitHub Pages or another host can be configured separately if desired; no hosting settings are changed by this guide.

## Maintain

- `geometry.js`: shared computational model, also used by the tests.
- `explorer.js`: SVG rendering and browser controls.
- `style.css`: responsive layout and presentation.
- `index.html`: explanations, formulas, and source links.
- `explorer.test.js`: dependency-free Node tests.

When formal coverage changes, update the theorem count here and in `index.html` to match the audit. Test the controls, keyboard inspection, browser console, and narrow layout after presentation changes. Mathematical wording should remain consistent with the short manuscript and verification guide.
