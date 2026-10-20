#!/usr/bin/env python3
"""Generate an annotated review copy; never alter the submission source."""
from pathlib import Path
import hashlib
import re
ROOT = Path(__file__).resolve().parent.parent
source = ROOT / 'reflecting_cells_fptas_short.tex'
s = source.read_text()
digest = hashlib.sha256(source.read_bytes()).hexdigest()
macros = r'''
\newcommand{\reviewnote}[3]{\par\medskip\noindent
\begingroup\setlength{\fboxsep}{6pt}\fcolorbox{#1}{#1!5}{%
\begin{minipage}{\dimexpr\linewidth-2\fboxsep-2\fboxrule\relax}
\small\textbf{#2}\par\smallskip #3
\end{minipage}}\endgroup\par\medskip}
\newcommand{\leanchecked}[1]{\reviewnote{cellblue}{LEAN CHECKED --- conditional}{#1}}
\newcommand{\humancheck}[1]{\reviewnote{cellorange}{HUMAN REVIEW}{#1}}
'''
s = s.replace(r'\begin{document}', macros + '\n'+r'\begin{document}',1)
s = s.replace(r'\end{frontmatter}',r'''\end{frontmatter}
\reviewnote{cellblue}{ANNOTATED REVIEW COPY --- not the submission version}{
Blue notes identify specific Lean conclusions under explicit hypotheses; they do not certify entire surrounding statements. Amber notes identify remaining proof obligations and attribution checks. All 108 declarations are covered by the axiom audit. Classical Markov estimates are assumptions, not proved here. The paper's finite decomposition, algorithm and running time are not fully formalized.}
\humancheck{Suggested reading order: (1) Lemma~\ref{lem:arrangement} and the cost accounting; (2) the integral-slice scaling and barycentric geometry and remaining complexity accounting; (3) the passage from the actual cells to the conditional Lean theorem; (4) the two Markov hypotheses; (5) the comparisons and citations. Check these arguments independently rather than treating a successful Lean run as evidence for them.}
''',1)
notes = {
 'thm:main':('human',r'The final error is checked by \texttt{shifted\_slack\_cover\_guarantee}: actual integer rows, closed shifted-slack widths, and integrality imply progression samples in the original polytope. Coverage, complete feasible candidates, extrema and Markov remain inputs. Chamber construction, enumeration, and runtime remain unverified.'),
 'cor:max':('lean',r'\texttt{nonnegative\_maximization} proves the scalar conversion from range-relative error to a multiplicative bound when the minimum is nonnegative. Check that the maximization instance satisfies its hypotheses.'),
 'cor:mixed':('lean',r'The new checks verify actual upward ceiling rounding, residual convex weights, the coordinatewise segment and grid identities, the ceiling multiplier, and the two-part error budget. The interval Markov inequality remains an explicit hypothesis. Integral-slice scaling, Carath\'eodory representation, the geometric assembly and total bit complexity remain human-review obligations. Polynomial scaling and the scaled feasible-set bijection are checked separately.'),
 'def:thresholds':('human',r'Check that every original integer point lies strictly inside $Q$, that closures of full-dimensional chambers cover $Q$ when it has interior, and that empty interior implies integer infeasibility. Overlap at subdivision hyperplanes is intentional. Lean verifies the shifted feasible-set equality and the lower slack bound; it does not construct $Q$ or the chamber cover.'),
 'lem:reflection':('lean',r'\texttt{integer\_row\_value} and \texttt{integer\_half\_shift} imply \texttt{shifted\_feasible\_iff}. \texttt{shifted\_slack\_integral\_progression} then derives feasible integer samples in the original polytope from weak shifted-slack interval bounds. \texttt{shifted\_slack\_cover\_guarantee} connects them to the final error. Check that actual closed chambers satisfy the interval hypotheses and cover the integer feasible set. Real extrapolated points need only lie in $\widetilde P$.'),
 'rem:slack-characterization':('human',r'The full if-and-only-if characterization is not checked in Lean. Verify both endpoint implications, zero-slack rows, and the strict versus weak inequalities.'),
 'lem:arrangement':('human',r'Check the chamber count $\sum_{j=0}^d\binom Hj$, its recurrence, and the two closed-halfspace enumeration with nonempty-interior tests. Zero normals must be removed first. Check compression to $2m$ bounds and rounding $[a,c]$ to $[\lceil a-1/2\rceil,\lfloor c-1/2\rfloor]$ for the original integer slack. Enumeration, rounding encoding bounds and runtime are not formalized.'),
 'lem:markov':('lean',r'\texttt{sampled\_markov} proves the displayed bound. The even-part identity and degree contraction are proved by \texttt{even\_contract} and \texttt{degree\_contract}; \texttt{symmetrized\_difference} proves the sharper half-degree constant. Only the centered and interval classical Markov derivative estimates are explicit external hypotheses. Check their scaling and degree parameters against Pierzchala Theorem~1.1.'),
 'prop:extrema':('lean',r'\texttt{eval\_restrict} and \texttt{degree\_restrict} construct the genuine multivariate line restriction. \texttt{multivariate\_selection} proves feasible minimum selection given a reflecting witness; the shifted slack-cover theorem derives its progression witness from rowwise slack widths, coordinate integrality, coverage and oracle completeness. The maximum follows in the paper by negating $f$; check that translation separately.'),
}
for label,(kind,text) in notes.items():
 pattern = r'(\\begin\{(?:theorem|lemma|proposition|corollary|remark|definition)\}[^\n]*\\label\{'+re.escape(label)+r'\})'
 m=re.search(pattern,s)
 if not m: raise SystemExit('Missing review anchor: '+label)
 note='\\'+('leanchecked' if kind=='lean' else 'humancheck')+'{'+text+'}\n'
 s=s[:m.start()]+note+s[m.start():]
s=s.replace(r'\begin{proof}[Correctness in Theorem',r'''\leanchecked{\texttt{ceiling\_refinement} proves positivity, $\ell\ge D^2$, and $D^2/\ell^2\le\eps$ for the actual maximum/ceiling choice. \texttt{slack\_cover\_guarantee} connects the rowwise geometry and integrality to the final error. \texttt{empty\_candidates\_iff} checks infeasibility conditional on sound and complete oracles.}
\begin{proof}[Correctness in Theorem''',1)
s=s.replace(r'\begin{proof}[Proof of Corollary~\ref{cor:mixed}]',r'''\leanchecked{\texttt{rounded\_barycentric\_weights} and \texttt{rounded\_segment\_weights} check the actual ceiling-rounded weights and construct nonnegative residual weights summing to one. \texttt{barycentric\_coordinate\_segment} checks the segment identity. \texttt{rounded\_grid\_coordinate} provides an explicit integer numerator over $k\Delta$. \texttt{markov\_grid\_multiplier} and its bounds theorem check the ceiling choice and half-error budget. \texttt{unit\_interval\_markov\_error} derives the segment estimate from the classical derivative bound. \texttt{markov\_grid\_transfer} checks the final error composition; the older Lipschitz and range-gap helpers are no longer needed.}
\humancheck{Check DHKW Lemma 9, the Carath\'eodory representation and choice of largest weight, convex membership from the residual weights, and the assembly of the scalar and coordinatewise Lean results. The construction and encoding size of $\Delta$, the logarithmic bound for $Q$, and total bit complexity are not formalized. Positive polynomial scaling, integer coefficients, degree, feasible-set identification, and scaled encoding bounds remain checked in ScaledPolynomial.}
\begin{proof}[Proof of Corollary~\ref{cor:mixed}]''',1)
s=s.replace("The coordinate and slack estimates in the proof",r"""\humancheck{External bound: CHKM, proof of Theorem~2.1, p.~29. Check the translation from their maximum inequality size to $(d+1)(\tau+3)$, the doubled shifted rows, extension from integer-hull vertices to integer points, and the separate $d=1$ case. The short version uses $\Phi=5d^2(d+1)(\tau+3)+2$. Lean's determinant estimates concern the different, sharper exponent retained in the long version; they do not formalize this imported bound.}
The coordinate and slack estimates in the proof""",1)
s=s.replace('Since $A,\\mathbf b$ are integral,',r'''\leanchecked{\texttt{integer\_row\_value}, \texttt{integer\_half\_shift}, and \texttt{shifted\_feasible\_iff} verify preservation of the integer feasible set for actual integer coefficient matrices. \texttt{shifted\_slack\_positive} proves the lower bound $1/2$. This shift is not a valid direct replacement for mixed-integer or continuous constraints.}
Since $A,\mathbf b$ are integral,''',1)
s=s.replace('Clear rational row denominators by multiplying each row by the product of its positive denominators.', r'''\leanchecked{Rational row normalization: \texttt{commonDen\_pos} and \texttt{clearedEntry\_real} construct positive product denominators and integer coefficients, including the right-hand side. \texttt{cleared\_domain\_iff} preserves feasibility under any domain restriction. \texttt{cleared\_payload\_quadratic} bounds a row's integer payload by $L(L+2)$ for rational payload $L$; \texttt{cleared\_matrix\_payload} sums these bounds. The arithmetic operation cost remains unverified.}
Clear rational row denominators by multiplying each row by the product of its positive denominators.''',1)
s=s.replace('It remains to account for bit operations.',r'''\humancheck{The rest of this complexity argument is not Lean checked. Reconcile the LP test count with the integer-oracle call count; verify Kannan's bound, objective evaluation cost, rational arithmetic and the absorption into $\varphi^{O(d)}$. An abstract existence theorem for a best candidate does not certify this algorithmic cost.}
It remains to account for bit operations.''',1)
s=s.replace(r'\section{Discussion and extensions}',r'''\humancheck{The integer-hull vertex observation and proposed extensions are not formally checked. In particular, low rank and nonpolyhedral domains are directions, not consequences of the current FPTAS.}
\section{Discussion and extensions}''',1)
s=s.replace(r'\begin{thebibliography}',r'''\humancheck{Reference audit: journal numbering for DHKW and Del Pia was checked against supplied published PDFs. The SODA page range has been completed. Piazzon--Vianello Propositions 1--3, Borwein--Erdelyi Theorem 5.1.8, and Pierzchala Theorems 1.1 and 1.4 were checked against the supplied full texts. Their continuous results do not certify the integer-range argument. Wei is retained as the user-supplied Optimization Online preprint; no arXiv record was located. The CHKM p.~29 locator was checked against the supplied published PDF. Still check the Stanley chapter DOI, PY metadata and Pak--Panova journal numbering. See \texttt{verification/reference\_audit.txt} for remaining source-access limitations.}
\begin{thebibliography}''',1)
out=ROOT/'reflecting_cells_fptas_review.tex'
out.write_text('% Generated by verification/make_review_draft.py\n% Submission source SHA256: '+digest+'\n'+s)
print(out)
