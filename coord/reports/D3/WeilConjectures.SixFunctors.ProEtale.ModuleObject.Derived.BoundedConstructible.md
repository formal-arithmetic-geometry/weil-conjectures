## What changed

Restored the tensor-preservation part of the returned B2 delivery and repaired its
`UpperStarUnitCoherence` consumer in the same delivery. The main module proves
`AlgebraicGeometry.ProEtale.CondensedRing.isMonoidal_boundedConstructible` from the tensor
unit and two finite truncation inductions. The single-sheaf base case is C4's existing,
proved `BoundedConstructibleTensorSingle`, used unchanged.

All declarations of the three new helper modules are proved:
`BoundedConstructibleDevissage`, `EllAdicBoundedTriangulated`, and
`BoundedConstructibleTensorPreservation`. The coefficient cases are continuous finite
extensions, their integral rings, supplied closed unit balls, and the algebraic closure.
The tensor unit is the actual regular coefficient module placed in degree zero.

The constructible Serre API would otherwise import the item through the public
base-change import in `CondensedFieldContinuousRealization`. Replace that import by
four defining APIs. Restore the necessary imports in four existing consumers and rename
one private scalar-extension helper to avoid collision with its newly imported public
namesake. The import-cycle change record gives every edit.

The completed monoidal instance retains the three geometric section instances that its
old sorry body omitted. Its internal-Hom and restricted monoidal consumers consequently
retain those parameters too. The private unit-coherence lemma must therefore retain
Z's geometric instances. The geometry change record prints the old and new inferred
interfaces. No target statement, coefficient ring, bounded-constructibility definition,
or ambient derived operation changes. Every existing public declaration and visibility
of `UpperStarUnitCoherence` is preserved.

The retained sandbox was compared with current shared sources. Its ten delivered Lean
files still contain the required proof and consumer adaptations. The change records
include all current transitive consumers and refreshed claim holders; all adapted
existing consumers are unclaimed. Earlier undelivered decompositions and verification
copies remain only in the scratchpad.

## Proved and sorry left

Holes closed: one of the main module's original three,
`AlgebraicGeometry.ProEtale.CondensedRing.isMonoidal_boundedConstructible`
(`lem-sfb-dc-tensor-preserves`).

Holes added: zero. Split-offs with sorry: zero. Two original holes remain unchanged:

- `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_rightDerivedLowerStar_obj`
  (`lem-sfb-dc-lower-star-preserves`).
- `AlgebraicGeometry.ProEtale.CondensedRing.isMonoidalClosed_boundedConstructible`
  (`lem-sfb-dc-hom-small-coefficients`).

All other delivered modules have zero holes. There is no sorry in a definition or a
private helper. The completed tensor proof uses existing recorded theorem inputs; this
is not a claim that the project's transitive axiom-free target criterion is established.

Edge cases: the unit has a presentation from rank zero to rank one, and zero homology
has a rank-zero presentation. Empty schemes and empty strata are included. Finite
truncation induction includes empty cohomological intervals. The ell-adic coefficient
restriction is retained; no tensor claim for arbitrary finite rings is made.

Fresh validation on 2026-10-19: `lcompile.py --all` compiled all ten delivered modules
with exit code zero and no warnings. `UpperStarUnitCoherence` took 55.6 seconds and the
main module took 45.3 seconds. All delivered Lean lines are at most 100 characters.
The four node copies have proof dependencies equal to the union of their steps' uses.

Resumed validation on 2026-10-19: the required `deliver3.py --no-push` returned
`OK (dry run)` at `78a9539c8b`, with review class `CODEX`. The complete delivered set
compiled and server preflight passed. The axiom probes of `CompatiblePrimitiveRoots`
and `UpperStarUnitCoherence` received no answer from the busy compile service; the
delivery tool explicitly leaves those probes to the merge checks. No launcher script
was changed, and no gate was bypassed.

## No longer needed

No existing module is withdrawn, and no whole-module pruning is claimed. The main file
adds one private proof import and retains its other imports for its original remaining
obligations. In particular the fifteen proof-dependency imports added to the shared
source since the early retained attempt are present unchanged.

Generic devissage uses `WeilConjectures.CategoryTheory.RingObjects.Ab` rather than a broad
Basic import. The tensor proof reuses the existing single-unit comparison and C4's
single-sheaf calculation.

The public import
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs`
is removed from `CondensedFieldContinuousRealization`. Its four replacement imports and
consumer adaptations appear in the import-cycle change record.

For `lem-sfb-dc-tensor-preserves`, the following direct dependencies are replaced by the
four helper nodes recorded in its updated proof:

`lem-weil-pbc-finite-type-over-noetherian`, `sk-def-sfb-constructible`,
`lem-sfb-integral-lfp-constant-model-comparison`,
`lem-weil-pbc-condensed-lfp-local-triviality`,
`lem-weil-pbc-condensed-qbar-lfp-local-triviality`, `sk-def-sfb-bounded-constructible`,
`lemma-constructible-pullback-stratification`, `sk-prop-sfb-cartesian-coefficients`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`sk-def-sfb-derived-categories`, `lem-weil-l-adic-extension-integers-dvr`,
`lem-sc-dvr-saturation-line-smith-normal-form`, `sk-def-sfb-condensed-ring`,
`sk-def-sfb-pullback-from-point`, `sk-def-sfb-pulled-back-coefficients`,
`lem-weil-pbc-site-pullback-abelian-exact`, `def-pc-kflat-complex`,
`def-weil-abstract-derived-category`, `sk-def-sfb-derived-tensor-hom`,
`sk-def-sfb-qlbar-condensed`, `lem-weil-pbc-noetherian-stratum-detection`,
`def-sbc-standard-tstructure-derived-category`,
`lem-weil-pbc-ringed-projection-mate-exact`, `det-lem-int-integral-heart-triangulated`,
`det-cor-coefficient-heart-ii-triangulated`.

Withdrawn tensor-node tool approvals:
`lem-weil-pbc-finite-type-over-noetherian`,
`lemma-constructible-pullback-stratification`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`lem-weil-l-adic-extension-integers-dvr`, `lem-sc-dvr-saturation-line-smith-normal-form`,
`lem-weil-pbc-site-pullback-abelian-exact`, `lem-weil-pbc-noetherian-stratum-detection`,
`lem-weil-pbc-ringed-projection-mate-exact`,
`lem-weil-pbc-condensed-lfp-local-triviality`,
`lem-weil-pbc-condensed-qbar-lfp-local-triviality`,
`det-lem-int-integral-heart-triangulated`, `det-cor-coefficient-heart-ii-triangulated`.

These are changes to the tensor node's direct proof dependencies and approvals. The
remaining obligations and the helper proofs may still use these nodes transitively.
The unit's tensor-preservation statement and its finite-truncation route are retained.

## Where the brief, the DAG or earlier work was wrong

The recorded B2 global failure is `UpperStarUnitCoherence:250`,
`cannot omit referenced section variable inst✝²`. This variable is the inferred
`LocallyOfFiniteType Z.hom` parameter of the bounded-constructible tensor unit. Retaining
Z's three geometry instances in that private lemma repairs the failure.

The earlier sandbox contained broader reductions adding three new holes. They are not
part of this delivery. The present repair closes tensor preservation without adding
holes and keeps the two original remaining obligations unchanged. The earlier finite
coefficient realization extraction is unnecessary for this repair and is not delivered.

Previous dry runs in this retained sandbox encountered delivery-tool preflight timeouts
after compilation succeeded. Those historical failures are recorded in the sandbox logs;
no launcher tool was changed or bypassed.

## Forced adaptations

`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence`:
the original error is line 250, `cannot omit referenced section variable inst✝²`.
Only the private omit clause changes: remove
`[LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]` from the omitted
list, retaining `[Fact ℓ.Prime]` there. The unchanged ambient composition-coherence proof
then compiles. No existing public signature or visibility changes. This consumer is
unclaimed. A fresh counterfactual compile of the current original consumer against the
repaired overlay failed in 44.8 seconds with that exact original error; the delivered
consumer compiles in the freshly verified set.

The import-cycle change record lists the four other existing adapted consumers,
the defining modules they need, and the scalar-extension private helper rename. All
four are unclaimed; their public signatures and mathematical definitions are unchanged.

## New nodes

- `lem-sfb-dc-module-devissage`: finite truncation induction specialized to constructible
  module objects, proved using `DerivedCategory.prop_of_bounded`.
- `lem-sfb-dc-ell-adic-triangulated`: coefficient-specific constructible Serre closure
  implies triangulated closure, proved for every ell-adic coefficient constructor.
- `lem-sfb-dc-tensor-unit`: the derived coefficient unit is bounded constructible, proved
  using `DerivedCategory.singleFunctorObjUnitIso` and explicit finite presentations.

Change records:

- `coord/changes/d3-bounded-constructible-import-cycle.md`.
- `coord/changes/d3-bounded-constructible-geometry.md`.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
