+++
id = "def-nagata-relative-gluing-datum-descent"
kind = "definition"
title = "Finite-stage raw relative gluing datum"
order = 358
uses = ["def-nagata-affine-fp-descent", "def-nagata-directed-finite-upper-bound", "def-nagata-morphism-descent", "def-nagata-qc-open-descent", "def-nagata-relative-finite-affine-presentation", "lemma-nagata-affine-fp-descends", "lemma-nagata-morphism-descends", "lemma-nagata-qc-open-descends"]
+++
**Status.** Bypassed by the formalized route: the finite-presentation and
Noetherian descent is done in one step by
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`
and `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`, so
this stage-by-stage bookkeeping is never carried out.

Descend every chart algebra in $\mathsf R_X$ using
[lemma-nagata-affine-fp-descends], every quasi-compact overlap open
using [lemma-nagata-qc-open-descends], and both directions of every
overlap isomorphism using [lemma-nagata-morphism-descends]. Define
$\lambda_{\mathrm{raw}}(X/S)$ to be the selected
upper bound of their finitely many stages, and denote the resulting raw
datum over $S_{\lambda_{\mathrm{raw}}}$ by
$\mathsf R_{X,\lambda_{\mathrm{raw}}}^{\mathrm{raw}}$.
Each object is transported by the canonical base-change map to the selected
upper bound. Functoriality supplies the comparison maps and coherence, so
the raw datum is well typed.
