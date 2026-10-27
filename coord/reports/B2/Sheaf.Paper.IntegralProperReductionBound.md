## What changed

Repaired the private `AlgebraicGeometry.ProEtale.integralLevel_isLE` proof in
`Sheaf.Paper.IntegralProperReductionBound`. Removed the derivation of an additive
instance for derived extension and the use of `Adjunction.homAddEquiv_zero`.
Instead the unit formula `Adjunction.homEquiv_unit`, `Functor.map_zero`, and
`comp_zero` prove that the hom equivalence sends zero to zero. This avoids the
failed search for monoidality on graded objects reported by the current global build.
The public declarations, definitions, imports, and theorem statements are unchanged.
The item's node records this local proof argument; all dependency edges are kept.

The current server queue (2026-10-27T14:00:54Z build of 8a67bde475) identifies this as
a zero-hole rework, with errors at lines 114 and 125. The shared snapshot initially
contained only an older bad-import error. The current source of the reduction-model
dependency was compiled before the item: 23.6 s for the model, 30.4 s for the
original bound. The repaired bound compiles with no warnings in 24.9 s. The final
import-order sandbox compile also passes: model 21.5 s, repaired bound 21.6 s.
The unchanged model copy was then removed from the delivery packet. No shared
interface was changed and no consumer adaptation is needed.

## Proved and sorry left

Assigned repair complete. Actual starting holes: 0; holes closed: 0; holes added: 0;
holes remaining: 0. No declaration contains `sorry`, and no statements were split off.
Both `AlgebraicGeometry.ProEtale.integralProperReductionBound_of_isNoetherian` and
`AlgebraicGeometry.ProEtale.integralProperReductionBound` retain their complete proofs.
The private `integralLevel_isLE` proof now establishes the needed zero comparison
without the failing additive-instance inference.

## No longer needed

The local synthesized `(Mod.extendScalars q).leftDerivedFunctor.Additive` instance
and `Adjunction.homAddEquiv_zero` are no longer needed. No module imports, DAG
nodes, or proof dependencies are pruned: the repair preserves the geometric and
finite-model proof route.

## Where the brief, the DAG or earlier work was wrong

The item was already zero-sorry, but the current running-build error makes it an
assigned repair. Compilation against published artifacts alone did not expose the
reported instance search. The old proof unnecessarily synthesized additivity of
derived extension to prove zero preservation; the additive right adjoint and the
adjunction's unit already suffice. There is no statement or definition correction.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
