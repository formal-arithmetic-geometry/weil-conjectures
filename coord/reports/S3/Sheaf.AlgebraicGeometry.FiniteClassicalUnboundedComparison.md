## What changed

Proved `AlgebraicGeometry.ProEtale.finiteClassicalUnboundedComparison` with its exact original
signature. The public imports are unchanged. All new helpers are private and fully proved.

Exact inverse image gives the classical image. The affine étale module bound supplies a
uniform bound on sections of classical fixed-ring module sheaves. A finite-interval induction,
products of K-injectives, and the existing generic left-completeness theorem extend the bound
to unbounded tails. Faithful exact restriction to the affine étale basis detects vanishing of
the derived comparison direct image. The truncation triangle and naturality of the actual
unbounded counit reduce each cohomology degree to the bounded-below counit. Its isomorphism
also supplies essential surjectivity.

Updated the existing node's proof, proof dependencies, proof origin, and removed obsolete
`tool_uses` entries. No definitions, public signatures, or other modules were changed.

Validation: the retained proof and unchanged direct consumer `UnboundedSiteComparison`
previously compiled together through `lcompile.py`. On resumption the required dry run
passed compilation, the axiom probe, and CODEX preflight. Later push attempts exceeded
the 60-second compile limit before submission. Profiling showed repeated category and
zero-morphism instance inference. Added local instances within the proofs to reuse those
structures and marked the private homology-comparison construction irreducible so
that consumers use its isomorphism interface. The resulting exact module compiled
cleanly in 34.8 seconds. No profiler
command is present in the delivery. The original theorem signature is textually identical,
and all lines satisfy the 100-character limit.

The change record covers module-local elaboration commands and lists downstream consumers.
The direct `ProEtaleSiteComparison` import is retained as part of the unit route.

Change record: `coord/changes/S3-finite-classical-unbounded-proof-context.md`.

## Proved and sorry left

Closed the single original hole in
`AlgebraicGeometry.ProEtale.finiteClassicalUnboundedComparison`
(node `lem-sfb-finite-classical-unbounded-comparison`). All three conjunction clauses are proved.

Holes closed: 1. Holes added: 0. Holes left in the item and delivery: 0.
No statements were split off.

## No longer needed

Removed these original direct proof imports:

- `Sheaf.AlgebraicGeometry.ProEtaleClassicalBounds`: use the more specific existing
  `Sheaf.AlgebraicGeometry.EtaleModuleAffineBound`. The latter still depends on the bounds;
  this is removal of a direct dependency, not a claim that those bounds are globally unused.
- `Sheaf.SixFunctors.UnboundedClassicalTruncation`: its public ringed-module interface has
  coefficients in `Type u`, whereas this statement uses fixed-ring coefficients in
  `Type (u + 1)`. Proved the required fixed-ring tail argument here using generic left
  completeness and the same finite-interval/product reasoning, without importing its
  coefficient presentation or its broader conclusion.
- `WeilConjectures.Algebra.Homology.BoundedBelowInjectiveResolution`: the proved canonical
  Plus compatibility and adjunction restriction APIs identify the two counits directly.
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`: use the existing canonical
  `Functor.rightDerivedFunctorObjQIso` and K-injective representative APIs; no separate
  existential total-derived-functor construction is needed.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`: the fixed-ring sheaf
  categories already have the required Grothendieck/K-injective instances; the separate
  ringed-site theorem is unnecessary.

Removed direct proof-dependency edges to `det-pe-unbounded-classical-bounds`,
`det-pe-unbounded-classical-truncation`, `lem-sc-bounded-below-injective-resolution`,
`lem-weil-pbc-kinjective-hom-derived`, `lem-weil-pbc-kinjective-total-derived`, and
`prop-pur-kinjective-resolutions-exist`. For the Hom computation, naturality of the existing
canonical derived functor suffices; no chosen chain-map representatives are constructed.
The five obsolete approved tool entries among those nodes were removed without adding or
reordering any approvals. Other global consumers may still need these nodes and modules.

No module leaves the targets' import closure: other consumers retain the removed modules.
The pruning above describes direct proof dependencies.

No additional presheaf-homology comparison node is needed: objectwise exactness followed by
exact sheafification proves the required vanishing directly. No modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically sound, but its ringed-module truncation theorem cannot
be applied directly to the fixed-ring coefficient universe of this item. The proof now
spells out the required argument for the actual categories, using the already proved generic
left-completeness theorem. The DAG and theorem docstring record that implementation.

The original Step 4's natural identification of homology with a sheafified presheaf is
stronger than needed. Exactness on the affine étale basis suffices for the truncation triangle
argument. There is no statement dispute, change of target meaning, or forced adaptation.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
