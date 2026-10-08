+++
id = "lemma-nagata-affine-gluing-identities-eventually"
kind = "lemma"
title = "The selected finite-stage datum satisfies the gluing axioms"
order = 337
uses = ["def-nagata-affine-gluing-valid-stage", "lemma-nagata-affine-gluing-coefficients-descend", "lemma-nagata-directed-finite-upper-bound"]
+++
**Status.** Bypassed by the formalized route: the finite-presentation and
Noetherian descent is done in one step by
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`
and `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`, so
this stage-by-stage bookkeeping is never carried out.

The overlap maps in $\mathsf G_{S,\lambda_{\mathrm{glue}}}$ preserve the
selected opens, are mutually inverse, and satisfy all identity and
triple-overlap cocycle equations.

## Proof

Every required equality is determined by finitely many generators after
localization. Equality in the colimit is witnessed at a finite stage.
The definition includes all those witness stages in one finite set, and the
selected upper-bound lemma makes every equation hold simultaneously at
$\lambda_{\mathrm{glue}}(S)$.
