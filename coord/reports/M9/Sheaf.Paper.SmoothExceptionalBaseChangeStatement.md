## What changed

Retained a complete proof script for
`AlgebraicGeometry.ProEtale.smoothExceptionalBaseChangeStatement` with its original
signature and canonical comparison map. It includes four private helpers:
`smoothExceptional_invertibleExponent`, `smoothExceptional_origin`,
`smoothExceptional_counit_isIso`, and `smoothExceptional_mate_isIso`.

The proof uses the ordinary-etale canonical smooth base-change theorem directly.
The remaining comparison-site mate is invertible because its unit is evaluated on a
bounded-below etale input and its counit on an etale-origin bounded-below object.
The finite-ring constructible origin theorem supplies that origin in the exact intrinsic
coefficient presentation used by the hypothesis. The exponent helper proves directly that
ell^n annihilates the actual level-n quotient and is a unit on the schemes.

Updated the item's node proof, proof dependencies and proof origin to this shorter route.
No statements, definitions, public signatures, coefficient domains or target signatures change.

The proof imports the source smooth-base-change module and the finite-ring origin module.
The four private helpers are proof-only declarations. Public statement imports and all
existing declarations are unchanged.

## Proved and sorry left

Closed the 1 assigned hole:
`AlgebraicGeometry.ProEtale.smoothExceptionalBaseChangeStatement`
(node `lem-pur-smb-extraordinary`). Added 0 holes and split off 0 statements.
No `sorry` remains in the sandbox module or its four private helpers.

The required resumed dry run passed on 2026-10-19:
`OK (dry run): commit 02a588804b compiles and passes the preflight; nothing pushed.`
The packet requires CODEX review because its node changes and it removes the private
proof import of `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel`.
The retained public source derived-comparison module supplies the actual comparison
unit theorem used by the proof, so the site-comparison step is retained.

## No longer needed

The explicit factorization of the canonical map avoids a separate transported
compact-support-counit computation. The source-library ordinary-etale theorem already
states invertibility of precisely the canonical transformation used by the definition,
for general Cartesian squares and all complexes over a quasi-separated base. Its use
retains the ordinary smooth base-change input of the unit. The finite-ring origin theorem handles the intrinsic
coefficient realization directly.

Removed proof imports (public statement imports retained):

- `Sheaf.AlgebraicGeometry.SfConstructibleExceptionalAdjointDischarge`
- `Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange`
- `Sheaf.AlgebraicGeometry.DerivedCategories`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`
- `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel`
- `Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion`
- `WeilConjectures.Compactification.NagataCompactification`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `WeilConjectures.Compactification.BaseChange`
- `Sheaf.Paper.ProEtaleConstructibleOrigin`
- `Sheaf.Paper.DerivedPullbackTensorHom`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived`
- `Sheaf.Paper.ComparisonPullbackExact`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange`
- `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`
- `Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom`
- `Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange`
- `Sheaf.Paper.CompactSupportExchangeTransport`
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`
- `Sheaf.Paper.SmoothMateCounitCancellation`

The following old direct proof dependencies are no longer needed by this module:

- `cor-sf-ambient-adjoint-discharge`
- `lem-kun-dimension-finite-type`
- `lem-pur-co-smooth-exchange-transport`
- `lem-pur-smb-mate-counit-cancellation`
- `lem-sf-class-compact-support-comparison`
- `lem-sf-comparison-pullback-exact`
- `lem-sf-proetale-constructible-origin`
- `lem-weil-pbc-comparison-pullback`
- `lem-weil-pbc-finite-type-over-noetherian`
- `thm-cbc-finite-level-proetale`
- `thm-sf-ambient-adjoint-class`
- `def-cbc-exchange-map`

These removals include the separate ambient class-adjunction/discharge, lower-bound
reflection for exceptional values, exchange-transport and mate-counit-cancellation branches.
The explicit canonical-map definition needs none of those extra identities: every one of
its displayed factors is already invertible. The source theorem requires a quasi-separated
base, supplied by local Noetherianity from finite type over the field, and a quasi-compact
base-changed vertical morphism, supplied by the Cartesian square.
No separate project Noetherian or dimension-bound declarations are applied.
The original coefficient-specific constructible-origin module is replaced by the existing
general finite-ring intrinsic origin theorem.

Removed obsolete tool-use entries:

- `lem-weil-pbc-finite-type-over-noetherian`
- `lem-kun-dimension-finite-type`
- `thm-sf-ambient-adjoint-class`
- `cor-sf-ambient-adjoint-discharge`
- `lem-sf-proetale-constructible-origin`
- `lem-weil-pbc-comparison-pullback`
- `lem-sf-comparison-pullback-exact`
- `lem-sf-class-compact-support-comparison`
- `thm-cbc-finite-level-proetale`
- `def-cbc-exchange-map`
- `lem-weil-pbc-transport-identifies-exchange`
- `lem-cbc-global-transport-chart-normalization`
- `lem-pur-co-smooth-exchange-transport`
- `lem-pur-smb-mate-counit-cancellation`

No module is withdrawn; these modules may still be needed by other items.

## Where the brief, the DAG or earlier work was wrong

The DAG plan is longer than required by the already-published definition of the canonical map.
The ordinary source theorem handles general Cartesian squares directly, and the comparison
mate can be checked factor by factor using its own definition. The retained attempt also
needed an explicit `IsIso` type in the ULift coefficient presentation: a fact indexed by
the defined type `P.Coefficient` was not found by
component instance search. No mathematical statement was corrected. The unit statement
and its ordinary smooth-base-change input remain intact. The source theorem requires
quasi-separatedness, supplied by local Noetherianity from the standing hypotheses.

Earlier attempts failed before elaboration because the published build lacked the
source smooth-base-change object file, or because the compile service did not answer.
The resumed required dry run now compiles the complete retained proof and passes
preflight. No dependency source, launcher script or shared repository file was edited.

Site comparison remains explicit: the retained public derived-comparison import
supplies `isIso_derivedComparisonAdjunction_unit_app`, used in both mate helpers.
The proof retains the unit's ordinary smooth-base-change input. No alternative ULA
criterion or new adjoint is used.

Edge cases: finite cohomological support may be empty, so the proof orders arbitrary
lower and upper bounds by minimum and maximum. The exponent ell^n works for every
positive level, without a ramification-divisibility assumption. The proof uses no
nonempty point set or restriction on the horizontal base change.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
