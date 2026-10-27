## What changed

Proved `AlgebraicGeometry.Etale.etaleSupportProjectionShiftUnit` using the existing
proper torsion and open compactification projection formulas, the compactification
shift instance and right-unit equation, and the exact-single constants comparison.
All original public declaration signatures are preserved. The abbreviation
`SupportProjectionCoherent` now specializes the identical generic conjunction in
`Sheaf.CategoryTheory.BifunctorProjectionCoherence`; this avoids expensive concrete
instance comparisons. See `coord/changes/P6-support-projection-coherence.md`.

Added `Sheaf.AlgebraicGeometry.DerivedTensorBraidingShift` with the generic canonical
signed braiding shift theorem (only a braided coefficient category is needed).
Its proof checks the Koszul signs on every cochain summand, descends along the
K-flat tensor comparisons, and transports by essential surjectivity. Updated
the item's proof route and dependencies.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.etaleSupportProjectionShiftUnit` (node
`lem-pur-etale-support-projection-shift-unit`): 1 of 1 original holes.
Added no holes. Both new theorems,
`DerivedCategory.canonicalTensorSymmetry_commShift` and
`CategoryTheory.bifunctorIsoCoherence`, are fully proved. No `sorry` remains in
any of the three delivered modules. No unfinished proof or split-off hole remains.
The clean full module compiled without warnings in 35.6 seconds; both companion
modules also compile within 60 seconds. The delivery tool runs the axiom checks.

## No longer needed

Removed these private proof imports from the item:

- `Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula`: use the proved upstream
  proper projection theorem directly (`lem-kun-0f0g` remains needed).
- `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection`:
  already publicly supplied by the existing compactification projection import;
  its mathematical result remains needed.
- `Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMonoidal`: the supplied
  compactification map already includes its established pullback comparison.
- `Sheaf.Paper.ProjectionMateExact` (`lem-weil-pbc-ringed-projection-mate-exact`):
  use the existing compactification shift and right-unit results directly.
- `Sheaf.Paper.DerivedAdjunctionShift` (`lem-weil-pbc-derived-adjunction-shift`):
  the existing canonical derived shift instances supply the required comparisons.
- `Sheaf.CategoryTheory.FiniteTypeConstantExact`
  (`lem-weil-pbc-finite-type-constant-exact`): exact constants and their derived
  comparisons are already available in the source library without a finite-type
  reduction.
- `Sheaf.AlgebraicGeometry.PullbackConstantModule`: use the actual canonical
  constant comparison already present in the source library.

The proof also does not need the separately stated nodes
`lem-kun-derived-pullback-composition-monoidal` and `lem-kun-pullback-constant`:
the upstream compactification and constant comparison APIs already provide the
specific comparisons used here. Removed these two proof-dependency edges.

Removed the five corresponding obsolete top-level tool approvals for the ringed
projection mate, derived adjunction shift, finite-type constant exactness,
monoidal pullback composition, and the separate constant-pullback invertibility lemma.
No existing module or declaration is withdrawn; existing transitive consumers and
the proper/open compactification route are preserved.

## Where the brief, the DAG or earlier work was wrong

The generic signed-braiding proof must be specialized with explicit
`Etale.sheafMonoidalCategory`, `Etale.sheafBraidedCategory`, and
`Etale.sheafMonoidalClosed` instances. An inferred specialization makes the kernel
compare nested sheaf localization proofs, taking about 26 seconds for that helper
alone. Explicit instances reduce it to a fraction of a second. The unit calculation
keeps `derivedTensorSymmetry` folded and uses its naturality with the separately
proved braiding/unit equations; unfolding the canonical braiding there was too slow.

The retained attempt had a temporary 5,000-heartbeat debugging limit on the unit
equation helper. Removed it and the new `BifunctorUnitEquation` alias: checking the concrete
equation through that alias causes a costly kernel conversion. The generic
coherence theorem now accepts the pointwise equation directly, proved using the
named unit arrows. The decisive repair is a private helper that takes an abstract
map and the forward shift/unit equations, specializing to the fixed map only after
applying generic coherence. The projection/coherence portion then compiles in
14.9 seconds. Removed the retained instance overrides and unused private helper.

No theorem statement correction. The unchanged coherence conditions are now
expressed through a generic predicate and two named unit arrows, preserving their
original mathematical meaning. This definition repair is recorded in
`coord/changes/P6-support-projection-coherence.md`. The DAG's coherence plan can use the source library's
already-proved compactification shift and unit API. The two constant-pullback
comparisons use different terminal objects, so their unit compatibility is proved
through their adjunctions rather than assumed to hold definitionally.

Edge cases: finite zero rings are covered by `isAddTorsion_of_finite`; no
nontriviality is introduced. The argument imposes no bounds on either complex,
uses all integer shifts directly, and permits empty schemes and identity
compactification factors. The summand calculation includes odd/odd Koszul signs.

## New nodes

`lem-pur-derived-tensor-braiding-shift`, in
`dag/nodes/sec-smooth-purity/lem-pur-derived-tensor-braiding-shift.json`, records
`DerivedCategory.canonicalTensorSymmetry_commShift`. This is the signed tensor coherence calculation needed to conjugate the existing projection
shift square. It is fully proved; no unfinished statement was split off.

`lem-pur-bifunctor-projection-coherence`, in
`dag/nodes/sec-smooth-purity/lem-pur-bifunctor-projection-coherence.json`, records
the generic inverse shift/unit cancellation theorem and its coherence predicate.
It has no holes. The definition refactor is recorded in
`coord/changes/P6-support-projection-coherence.md`.

## Second reading by P6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
