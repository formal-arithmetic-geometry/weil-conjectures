+++
id = "lemma-nagata-affine-gluing-coefficients-descend"
kind = "lemma"
title = "All gluing coefficients occur at the selected stage"
order = 335
uses = ["def-nagata-affine-gluing-coefficient-stage", "lemma-nagata-directed-finite-upper-bound", "lemma-nagata-finite-affine-gluing-presentation", "lemma-nagata-ring-finite-type-subalgebras"]
+++
**Status.** Bypassed by the formalized route: the finite-presentation and
Noetherian descent is done in one step by
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`
and `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`, so
this stage-by-stage bookkeeping is never carried out.

Every selected finite coefficient subalgebra, basic-open element, restricted
overlap map, and proposed inverse is defined at
$\lambda_{\mathrm{coeff}}$. Under base change to the original chart rings,
these objects are the corresponding restrictions of the data in
$\mathsf G_S$.

## Proof

Each finite coefficient list lies in one finitely generated
$\mathbf Z$-subalgebra by
[lemma-nagata-ring-finite-type-subalgebras]. The selected upper bound
dominates every such stage by
[lemma-nagata-directed-finite-upper-bound]. Hence all selected
coefficients and restricted maps are simultaneously defined at the named
common stage, and base change returns the original finite lists. The full
chart rings are recovered only after taking the filtered colimit over all
finite refinements; no single stage is asserted to contain every coefficient
of an arbitrary chart ring.
