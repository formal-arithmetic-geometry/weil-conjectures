## What changed

Proved `directImageReductionUnit` using normalized augmentation transport and a
counit-compatible comparison with the existing original-site strict reduction model.
The comparison starts from the canonical constant-to-function quotient ring
isomorphisms, preserves all quotient transitions and ordinary pullback squares,
and descends through the universal derived counits. Naturality of adjunction mates
transports the existing strict projection isomorphism. Mate pasting identifies its
finite evaluations with the specified `finiteProjection`.

Validation: the complete module compiled cleanly through `lcompile.py` in 34.9 seconds.
A generic derived-model helper packages counit invertibility and normalization before
specialization, avoiding repeated conversions of concrete sheaf constructions. Local
irreducibility settings retain the construction APIs, and the exact unique-existence
choice specification fixes the normalized pullback comparison.

No target, public statement, or existing definition was changed. The DAG proof route
was updated to record the original-site model comparison.

## Proved and sorry left

Closed the one original hole (1 closed, 0 added):
`AlgebraicGeometry.ProEtale.StrictTower.DirectImageReduction.directImageReductionUnit`.
No holes added and no holes remain in the delivered module. No statements split off.
The existing dependency
`AlgebraicGeometry.Scheme.OrderedExchange.quotientProjection_isIso`
(node `lem-sp-constant-perfect-quotient-projection`) remains a named hole in its own
module; this delivery uses the existing `projection_isIso` proved from it.

## No longer needed

The proof does not instantiate `constantPerfectProjectionModels` or
`constantPerfectProjectionIdentification` of
`Sheaf.Paper.ConstantPerfectProjectionModels`
(node `lem-sf-cbc-constant-perfect-projection-models`). Their equal site/morphism/coefficient
universe interface does not directly apply to the original pro-etale site used here.
The existing original-site perfect-quotient projection route supplies the needed
invertibility, and the new comparison proves that it applies to the specified map.

The direct proof no longer needs its own levelwise cohomology detection argument:
that argument is already proved in `Sheaf.Paper.ProEtaleConstantReductionTower`.
The nodes `lem-weil-tower-category-levelwise-abelian` and
`lem-weil-pbc-unbounded-derived-iso-cohomology` remain transitively needed there.
Removed the proof-only imports `Sheaf.Paper.RingedSitePerfectProjectionFormula`,
`Mathlib.Algebra.Homology.DerivedCategory.HomologySequence` and
`Mathlib.CategoryTheory.Abelian.FunctorCategory`; the proof uses the already established
strict projection theorem and mate-pasting instead.
No module or declaration is withdrawn. The new proof uses the existing nodes
`def-sp-constant-reduction-models`, `lem-sp-completion-mate-comparison` and
`lem-sp-constant-perfect-quotient-projection`, all in the same unit `sk-prop-sf-cbc`.

## Where the brief, the DAG or earlier work was wrong

The planned direct application of the constant perfect projection models omits a
universe/interface comparison: that theorem uses equal small-site universes,
whereas this item uses the original pro-etale site with different object and
morphism universes. The proof instead explicitly compares the two existing
original-site reduction presentations before taking adjunction mates. Naturality
and completion-unit normalization need no completeness assumption on the input.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
