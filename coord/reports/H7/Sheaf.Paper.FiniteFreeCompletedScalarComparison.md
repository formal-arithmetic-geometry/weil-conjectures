## What changed

Proved the canonical chain-comparison existence and uniqueness theorem and both
identity multiplication/unit existence and uniqueness theorems in
`Sheaf.Paper.FiniteFreeCompletedScalarComparison`.

The chain map is built from explicit sheafified scalar-comparison maps to each
quotient. Their transition compatibility gives a product map killed by one minus
the shift. Its mapping-cocone lift has zero shifted component. The two cone
projections and tensor generators give uniqueness. For identity coefficients,
tensor multiplication and its inverse construct the normalized completeness unit.

All existing public statements, definition bodies and docstrings are preserved.
The command/instance-search adjustments are documented in
`coord/changes/finite-free-completed-scalar-proof-commands.md`.
New helpers are private and proved. The proof uses the current explicit
`integralScalarReductionIso` interface, replacing an earlier candidate based on
the old chosen reduction witness. The DAG records the construction argument and
retains the entire open finite-free completeness plan.

## Proved and sorry left

Closed three of the five original holes:

- `WeilConjectures.completedScalarChainComparison_existsUnique`.
- `WeilConjectures.completedScalarIdentityMultiplication_existsUnique`.
- `WeilConjectures.completedScalarIdentityUnit_existsUnique`.

Two original holes remain, both attached to node
`lem-weil-finite-free-completed-scalar-comparison`:

- `WeilConjectures.completedScalarComparison_existsUnique`.
- `WeilConjectures.finiteFreeCompletedScalarComparison`.

Added holes: zero. Split-off theorems: zero. The original coefficient-map proof
is preserved. The whole delivered module compiled without warnings in 36.7 s.
The main theorem retains its original source and complete natural-language proof.
The descent candidate was not retained because its specialization of the counit
still exceeds the checking budget; its original named hole is preserved.

## No longer needed

Removed these direct proof imports, which the completed construction proofs do
not need (some remain available transitively):

- `Mathlib.Analysis.Normed.Unbundled.SpectralNorm`.
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`.
- `Mathlib.Topology.Algebra.Valued.LocallyCompact`.
- `WeilConjectures.RingTheory.FiniteOverCompleteRing`.
- `Mathlib.LinearAlgebra.FreeModule.PID`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`.
- `Sheaf.Paper.ConstantCompletionEquivalence`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`.
- `Sheaf.CategoryTheory.RingedSiteModules`.
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`.
- `Sheaf.Paper.DerivedComplete`.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit`.
- `Sheaf.CategoryTheory.RingedKoszulCompletionReflector`.
- `Sheaf.Algebra.Homology.KFlat`.
- `Sheaf.Paper.ExtendedCechCompletionModel`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`.
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`.
- `Sheaf.Paper.DerivedCompleteOnSlices`.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`.
- `Sheaf.Paper.IntegralReductionTowerCanonical`.
- `Sheaf.Paper.WeilCompletedTensorReflector`.
- `WeilConjectures.Algebra.Homology.RoosComplex`.
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`.

`Sheaf.Paper.IntegralScalarExtensionWellDefined` is retained as a private
`import all` so that its explicit scalar-reduction proof API can be used.

No modules are withdrawn and no mathematical dependency of the remaining main
theorem is declared obsolete. Its five-step route is retained. The generic
finite-free, regular-quotient, unit-power, and integral-basis nodes remain needed
by that open argument. The new proof directly imports scalar-comparison descent,
integral-operations Roos constructions, the explicit scalar-reduction API and
signed cocone map formulas.

## Where the brief, the DAG or earlier work was wrong

No false statement was identified. The proposed main assembly still needs
concrete identifications between completed coefficient sheaves and the generic
adic-basis/regular-quotient models, including scalar actions, canonical units,
and independent site/coefficient universes.

The reduction dependency changed during this session from a chosen ordinary
functor to an explicitly constructed tensor functor. The proof was adapted to
its current isomorphism and naturality API and the full module recompiled.

The compile service was frequently busy. A transient missing published
`DerivedCompleteUnrestricted.olean.server` artifact also affected the unchanged
original module; a later baseline check passed, and work resumed. This is no
longer a blocker.

Earlier attempts: the first delivery attempt exhausted the delivery tool's own slot wait and
reported all 24 slots occupied. The second attempt terminated with exit 143
without output. The third attempt also terminated with exit 143 and no output. Nothing was
pushed by those earlier attempts. On resumption the delivery tool reached server
preflight and requested a change record for the added commands and attributes.
This is supplied as `coord/changes/finite-free-completed-scalar-proof-commands.md`,
including the complete transitive consumer list and current claim holders.

The next delivery call reached its 50-minute admission wait limit with all 20
delivery slots occupied and returned `DELIVERY BUSY` (exit 75). The packet remains
ready for the required retry; this was not a proof or preflight failure.

Two subsequent delivery calls obtained admission but exited before a successful
preflight because the compile service returned no answer within 645 seconds.
Neither pushed anything. Further counit/descent experiments remain in scratch;
the submitted Lean packet still closes three original holes and adds none.

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
