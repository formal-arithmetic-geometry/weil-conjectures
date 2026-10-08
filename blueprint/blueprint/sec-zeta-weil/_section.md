+++
id = "sec-zeta-weil"
kind = "section"
title = "Zeta Functions and the Weil Conjectures"
order = 2852
uses = ["sec-deligne-laumon-a1", "sec-deligne-laumon-general", "sec-poincare-duality", "sec-proper-base-change", "sec-purity-real-sheaves", "sec-six-functors", "sec-smooth-base-change", "sec-smooth-purity", "sec-trace-formula"]
+++
content: zeta series, rationality, Frobenius factors, and the assembled Weil statements.  
key results: Theorems [sk-thm-weil1]–[sk-thm-weil5].  
references: `zeta_weil_brief.tex`; detailed-source identifiers below
are retained as provenance. The three abstract inputs remain explicit; all
three are now reduced to results of this document.

This is the brief blueprint of the *zeta-function and power-series*
layer: how the three abstract inputs — the
Grothendieck–Lefschetz **trace formula** ([sk-thm-trace-formula] and
[sk-thm-trace-transport] of §[sec-trace-formula]),
**Poincaré duality** ([sk-thm-poincare-duality] of
§[sec-poincare-duality]), and the **weight estimate** (Deligne
purity, [sk-input-weights]) — produce the five Weil conjectures. Per the readme conventions, *every node is a separate
proposition* (no bundled conclusions): the trace series and its logarithm, the
closed-point Euler product, the trace-to-determinant factorization, the
rationality criterion and its descent, the root-purity statement, the weight
separation, the duality reciprocity, and the five final statements are all
stated on their own. Statements list definitions in `\\
uses`, proofs cite with `\\ Cref`, and no quoted input
remains. Everything below is on the
zeta side; the cohomological side (six operations, purity, duality) is
referenced, not reproduced.
