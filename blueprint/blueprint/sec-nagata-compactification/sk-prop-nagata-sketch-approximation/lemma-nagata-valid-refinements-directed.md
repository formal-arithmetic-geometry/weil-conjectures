+++
id = "lemma-nagata-valid-refinements-directed"
kind = "lemma"
title = "Valid finite coefficient refinements form a directed set"
order = 339
uses = ["def-nagata-noetherian-stage", "lemma-nagata-affine-gluing-identities-eventually", "lemma-nagata-directed-finite-upper-bound", "lemma-nagata-filtered-colimit-finite-data"]
+++
**Status.** Bypassed by the formalized route: the finite-presentation and
Noetherian descent is done in one step by
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`
and `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`, so
this stage-by-stage bookkeeping is never carried out.

The valid finite coefficient refinements occurring in
[def-nagata-noetherian-stage] are nonempty and directed under
inclusion. If $\lambda\leq\mu$, inclusion of coefficient algebras induces
compatible affine chart maps $S_\mu\to S_\lambda$; these maps satisfy the
identity and composition laws.

## Proof

The selected valid stage is one object. Given two valid refinements, take
the union of their finite coefficient lists and then a common upper bound of
the finitely many stages witnessing their gluing equations. The finite-data
lemma makes the resulting refinement valid and above both inputs. Inclusion
of coefficient rings induces the affine maps on every chart. Their
restrictions agree on overlaps by the gluing equations, so they glue; the
identity and composition laws hold chartwise and therefore globally.
