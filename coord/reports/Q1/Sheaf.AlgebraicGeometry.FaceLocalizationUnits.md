## What changed

Proved `Algebra.isAddUnit_addLocalization_iff_face` in
`Sheaf.AlgebraicGeometry.FaceLocalizationUnits`, retaining its exact signature and
following both elementary steps of `lem-trf-face-localization-units`.

For a unit, write the element and its inverse as fractions. Their sum being zero
provides an equality after adding a face denominator. The same equality in the
localization at the top submonoid, followed by the given injectivity hypothesis,
gives `q + q' = f + f'` in the original monoid. The face property puts `q` in the
face. Conversely, swap the two face elements to exhibit an additive inverse;
commutativity and `AddLocalization.mk_self` prove their sum is zero.

The statement needs only `Mathlib.GroupTheory.MonoidLocalization.Basic`, now its
sole public import. Import cleanup is recorded in
`coord/changes/face-localization-units-imports.md`. The direct consumer
`Sheaf.TraceFormula.FsFaceSharpening` independently obtains both removed imports
through its existing public import of `Sheaf.TraceFormula.FaceLocalizationFs`.

Searches actually run: LeanFinder for units of localization at a face (generic
localization unit lemmas only); Loogle for `AddLocalization.mk_eq_mk_iff` (exact
fraction equality API); msearch grep for the face-unit characterization (no hits),
and source searches in Mathlib, WeilConjectures and Sheaf. No exact existing
face-specific theorem was found.

## Proved and sorry left

Closed one of one holes: `Algebra.isAddUnit_addLocalization_iff_face`
(node `lem-trf-face-localization-units`). Zero holes remain in the item; zero
holes added; zero statements split off. The proof uses only proved Mathlib
lemmas. Server single-file compilation succeeded both before and after import
cleanup. `#print axioms` reports exactly `[propext, Quot.sound]`. The unchanged
direct consumer `Sheaf.TraceFormula.FsFaceSharpening` also compiled against the
reduced module using server `lcompile.py --all`; its temporary sandbox copy was
removed before delivery.

## No longer needed

Removed the public imports `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup` and
`Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup`, replacing them with
`Mathlib.GroupTheory.MonoidLocalization.Basic`. Neither log schemes nor the
additional group-completion API is used by this theorem.

No DAG nodes or modules are withdrawn. The statement dependency
`def-trf-fs-log-blowup` remains: it supplies the mathematical meaning of integrality
and group completion, though its Lean log-geometric module is unnecessary here.
The existing `proof_deps = []` and the two elementary proof steps already match
the proof, so no node edits are needed. Both removed modules remain needed by
other consumers, including `FaceLocalizationFs`; no global pruning of them is
claimed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The original module imported substantially more
than its statement or proof requires. The planned elementary argument suffices,
without additional dependencies or new nodes. The unit's route is preserved.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
