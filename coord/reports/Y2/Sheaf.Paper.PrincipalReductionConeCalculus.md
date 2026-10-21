## What changed

Constructed the uniformizer endomorphism by pointwise multiplication on sections, and
proved its module linearity and section formula. Constructed the strict scalar-cone endofunctors, the scalar transition maps and cone
coaugmentations in `Sheaf.Paper.PrincipalReductionConeCalculus`. Proved their degreewise
coordinate formulas, functoriality, coaugmentation compatibility and preservation of
quasi-isomorphisms. Constructed the signed double-cone interchange and coherent integer
shift comparison, with naturality, transition compatibility, cone inclusion, boundary,
and coaugmentation equations. The original theorem and all public signatures stay
unchanged; its conjunction is assembled from these proofs and the normalized derived
comparison below. All new construction helpers in the item module are private and proved. The cone
calculus is assembled through a generic abelian-category API in the same module, so
its specialization does not repeatedly unfold the concrete sheaf-module category or
the scalar action through pullback and unitors. The scalar-action multiplication law
is proved before that construction is made locally irreducible in this proof section.

Isolated the distinct derived principal-quotient normalization argument in
`Sheaf.Paper.PrincipalReductionDerivedNormalization`. This retains the two-term free
coefficient resolution route: it identifies the strict cone with the existing derived
extension followed by restriction, identifies the quotient transition and actual adjunction
unit, and records the compatible derived shift and triangulated structure. No chosen
objects in a definition depend on this unresolved theorem. Updated the parent proof route
and added its node. The module-command interface record is
`coord/changes/Y2-principal-reduction-proof-context.md`; it lists all downstream users.
The helper scalar-shift instance is local to the generic proof section.

## Proved and sorry left

Closed the original body of
`AlgebraicGeometry.ProEtale.PrincipalReduction.principal_reduction_cone_calculus`
(node `lem-pe-principal-reduction-cone-calculus`) by a complete assembly from the strict
cone calculations and the following separate theorem.

One new hole remains:
`AlgebraicGeometry.ProEtale.PrincipalNormalization.derived_principal_normalization`, in
`Sheaf.Paper.PrincipalReductionDerivedNormalization`, node
`lem-pe-principal-reduction-derived-normalization`.

This is a decomposition of one original hole into one strictly narrower hole, with net
hole reduction zero. The new statement contains only the normalized derived comparison;
it contains no strict endofunctor construction, four-coordinate cone interchange,
coherent strict shifts, cone boundary computation, or naturality/tower/coaugmentation
calculus. Those parts are proved in the item module. No other hole is introduced. Both modules were compiled together in import order;
the required delivery command performs the final clean compile, axiom probe and preflight.

## No longer needed

The item no longer directly imports
`Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients`,
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`, or
`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`.
Their nodes `lem-weil-pbc-independent-bounded-flat-kflat`, `lem-pc-kflat-resolution`,
and `lem-weil-pbc-site-derived-tensor-descent` remain dependencies of the new derived
normalization result, so none is withdrawn from the library. The same applies to
`def-pc-tensor-complex-sheaves`: it is needed for that separate tensor computation.
The parent no longer needs a separate triangulated-category argument: the new normalized
derived result supplies it. Its generic triangulated-category input remains needed below.
The existing approvals for those tensor inputs remain unchanged: the resolution
route still needs them through the normalization result. No modules or nodes are
withdrawn, and no adopted source declarations are removed.

## Where the brief, the DAG or earlier work was wrong

The resolution theorem already provides the scalar and an unnormalized natural
comparison with tensoring by the pulled-back quotient. That comparison alone does not
identify the canonical extension/restriction functor or its prescribed derived adjunction
unit and integralStep. Treating those as definitionally identical would omit a real
normalization argument; this is the remaining separate result.

The signed interchange has been checked against Mathlib's negative-projection cone
boundary, including the sign on the fourth coordinate. No mathematical statement or
definition repair is proposed. The unit's rank-one-resolution route is retained.

## New nodes

`lem-pe-principal-reduction-derived-normalization` records the normalized derived
coefficient computation, its canonical transition and unit, and its compatible derived
shift. Source: the resolution proof, On X paragraph, and the first-reduction proof, Cones
paragraph.
It is strictly part of the original argument, excluding the strict cone calculus now
proved. Its docstring gives the full mathematical proof and tests zero complexes,
negative shifts, and empty schemes. The proof-context commands are recorded in
`coord/changes/Y2-principal-reduction-proof-context.md`; no existing public statement
or definition changes.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
