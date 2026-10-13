# Follow-ups from the master → slopmaster merge (master at `35be017`)

The merged tree builds (`lake build`, 9750 jobs, no errors). The items below are workarounds
to revisit, unverified explanations, and cleanup left over from the merge.

## Workarounds that should become proper fixes

- **`DeligneLaumon/Reduction/DirectImage.lean`**: `LocallyQuasiFinite c` is now proved by hand
  (`IsClosedImmersion.spec_of_surjective`, then `instLocallyQuasiFiniteOfIsImmersion`), because
  the unguided instance search times out. The search goes `LocallyQuasiFinite` →
  `LocallyOfFiniteType` → `HasCompactification.locallyOfFiniteType`
  (`Compactification/Defs.lean`) → the Nagata `HasCompactification` instance
  (`Compactification/NagataCompactification.lean`), and from there into hundreds of
  ring, field and order instances on `CommRingCat.of A'`. Consider lowering the priority of
  `HasCompactification.locallyOfFiniteType` or of the Nagata instance, or demoting one of them
  to a lemma. Other `LocallyOfFiniteType` / `LocallyQuasiFinite` searches are probably slowed
  down by the same path.
- **`WeilSheaf/Cohomology.lean`**: the new instance
  `(X ↘ Spec (CommRingCat.of k₀)).IsOver (Spec (CommRingCat.of k₀))` is only needed because
  `Spec k₀` now gets its structure over itself from mathlib's `specOverSpec`, not from the
  trivial `OverClass X X`. It holds for any `X.Over (Spec R)`, so it belongs in a general file
  next to the `Over` API, or upstream in mathlib.
- **`GrothendieckAbelian/SerpeCardinal.lean`**: `fact_isRegular_serpeCardinal` is now
  `scoped` in `CochainComplex`. Globally, it matched every `Fact κ.IsRegular` goal with `κ`
  unknown and started a search over all categories that never terminated, which broke the
  `EssentiallySmall X.ProEt` and `MonoidalCategory (Sheaf …)` searches. Any new user of the
  instance must `open CochainComplex`, or pass it explicitly.

## Explanations not yet verified

- Why slopmaster's own `TraceFormula/Adic.lean` didn't hit the `SerpeCardinal` loop before the
  merge. The likely cause is that its imports changed from `Complete.RationalCoefficient` to
  `Complete.IntegralCoefficient` + `Rationalization`, which pulls in the accessible-category
  instances that open up that search route. The import chain hasn't been traced.
- Which master import brings `specOverSpec` into `WeilSheaf/Cohomology.lean`.
- Which side of the merge made `ULift.up` need an explicit universe level in
  `WeilSheaf/Tensor.lean`.

## Edits included that were already in the working tree

These edits were in the working tree before the build fixes. They're part of the build that
passed, and the author should review them:

- `Mathlib/CategoryTheory/MorphismProperty/OverAdjunction.lean`: `Over.pullbackCongr_refl` is
  no longer `@[simp]`.
- `SixFunctors/UpperLowerStar/Defs.lean`: the two `lowerStarComp_id_*` proofs pass that lemma
  to `simp` explicitly.
- `SixFunctors/Etale/Derived/Shift.lean`: `commShiftRightDerivedUpperShriek` moved into the
  `Monoidal` section.
- `SixFunctors/Etale/Derived/Localization.lean`:
  `isIso_rightDerivedUpperShriekAdjunction_unit_app` gained the monoidal coefficient
  hypotheses.
- `SixFunctors/Etale/Gabber.lean`: adds `import Mathlib.CategoryTheory.Sites.EpiMono`.

## Cleanup

- Long-line linter warnings (over 100 characters):
  - `SixFunctors/ProEtale/FiniteCoefficient/Derived/Comparison.lean:26`
  - `SixFunctors/ProEtale/FiniteCoefficient/Derived/TorAmplitude.lean:18`, `:19`
  - `SixFunctors/ProEtale/ExceptionalAdjoint.lean:62`
- There is no CI baseline on master: the last five `build` runs on master were cancelled.
  Re-run CI on master to confirm master builds on its own.
- master has moved on since this merge (`origin/master` is at `ffec648`), so the next merge
  will bring in more.
- Blueprint: PR #1432 (auto-bump the `blueprint` submodule) is open against master.
  slopmaster still pins `blueprint` at `3f088f1`. Once #1432 is merged, the "Bump Blueprint"
  workflow updates both branches.
