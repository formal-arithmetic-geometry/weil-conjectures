## What changed

Separated the unchanged comparison interface into
`Sheaf.Paper.IntegralPullbackCompletedComparisonData`, re-exported by the assigned
module. This breaks the dependency cycle when proving the two presentations of
the finite tower separately. All existing mathematical names, elaborated types and definition bodies
are preserved; the finite complex comparison has an explicit return
annotation and retains its two original local additive bindings. Local transparency
settings prevent repeated expansion of large coefficient structures. The change record records their text and consumers.

Reviewer correction: the elaborated types are preserved only up to definitional
equality. `integralComputation`, `integralProjection`, `finiteComputation`,
`finiteComplexComparison` and `Comparison.projections` now elaborate the
`HasDerivedCategory` instance as `integralTowerHasDerivedCategory` instead of
`integralOperationsCommHasDerivedCategory` (both `HasDerivedCategory.standard _`), and
`Comparison.mk.inj`, `Comparison.mk.injEq`, `Comparison.mk.sizeOf_spec` are no longer
generated. All twelve direct importers compile. The reviewer also removed four unused
imports of `CompletedIntegralFiniteTowerTransport` (its statement is `sorry`) and added
the two coefficient definition nodes whose characterizing lemmas step 1 uses to the
item's `proof_deps`.

The comparison is assembled through the total derived limit of the retained
finite-pullback derived pair. Intrinsic completeness follows from the existing
coefficient-completeness transport. Naturality follows by cancellation through
the two realization isomorphisms; the projection equation follows by composition
of their two normalization equations; the shift equation follows by conjugation.

The signed chain shift uses product shifts and the signed mapping-cocone shift.
The finite-tower comparison supplies compatibility with the strict transitions.
The shift descends along the resolving localization of good complexes.

## Proved and sorry left

The original hole is
`WeilConjectures.IntegralCompletedComparison.integralPullback_completedComparison`.
Its new body is an assembly from separate realization results. This is a
**decomposition**, not a net reduction of the sorry count.

The two newly retained holes are:

- `WeilConjectures.IntegralCompletedComparison.integralPullback_roosFiniteTower`:
  node `lem-a1-integral-roos-finite-tower-realization`;
  the integral Roos presentation, including its actual derived-limit projections
  and the specified shift. This statement concerns every integral input and does
  not use completed pullback or intrinsic completeness.
- `WeilConjectures.IntegralCompletedComparison.completedIntegral_finiteTowerTransport`:
  node `lem-a1-completed-integral-finite-tower-transport`;
  transport of the published strict tower, finite quotient-unit normalization,
  its projections, and the actual completed shift. This statement does not use
  integral Roos pullback or a comparison to it.

`WeilConjectures.IntegralCompletedComparison.integralPullback_signedShift`
has a proof with no new hole. No definition or private helper contains a sorry.

All five delivered modules, including the signed shift, interface and final assembly,
compile without errors or warnings against the current published build.
The original module has zero holes; two named holes are added in the separate
realization modules (one original hole closed, two holes added, net minus one). The attempted proof of the unnormalized
Roos isomorphism compiled, but it does not establish the actual projection and
retained-shift equations. Its unused helpers are omitted from the delivery.

## No longer needed

No module is withdrawn. No source-library declaration is removed or weakened.
The original long list of proof imports is replaced by the coefficient
completeness theorem and the two realization modules plus the signed-shift
module. The old lower mathematical dependencies needed to prove the two
realization results remain needed transitively; this delivery does not claim
that those modules are pruned.

Removed direct proof imports (some remain transitive dependencies):

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`.
- `Mathlib.CategoryTheory.Sites.Sheafification`.
- `Mathlib.Topology.Algebra.Valued.LocallyCompact`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`.
- `Sheaf.Algebra.Homology.DiagramKFlatReplacements`.
- `Sheaf.Algebra.Homology.KFlat`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`.
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`.
- `Sheaf.CategoryTheory.StrictRoosComparison`.
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`.
- `Sheaf.Paper.ConstantCompletionEquivalence`.
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`.
- `Sheaf.Paper.IntegralOperationsWellDefined`.
- `Sheaf.Paper.KFlatRingedToposPullback`.
- `Sheaf.Paper.KoszulReconstruction`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct`.
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`.

The assigned theorem no longer directly needs the detailed DVR, finite-free
scalar, Koszul reconstruction, K-flat replacement, tensor balancing, strict-Roos
or derived-limit constructions: their separate realization statements retain
those obligations. The comparison interface still publicly imports exactly the
original public dependencies.

## Where the brief, the DAG or earlier work was wrong

The original proof plan did not provide a single declaration identifying both
coefficient presentations with the same actual finite-tower derived pair while
retaining every projection and the specified shifts. An abstract Roos
isomorphism does not itself establish equality with the actual
`completedRlimProjection`. The two new realization nodes isolate these distinct
requirements without changing the assigned statement.

No target signature or mathematical definition was repaired.
The first delivery check timed out in the extracted interface, before pushing.
The interface now pins additive-sheaf instances and freezes large derived-category
structures locally. It also disables unused automatic constructor-injectivity and
size-specification helper lemmas for the large comparison record, after checking
that no consumer uses them; the constructor, fields and recursors are preserved.
Edge cases checked for the two splits: the zero complex gives the zero projection
identities; index zero is the first positive quotient, with no exponent-zero
quotient; no boundedness, immersion, or invertibility of the completed structural
ring map has been added. Both realizations retain all input derived objects and
all the original representative computations. The only interface
change is the relocation described above. Instance choices in the new proofs
are pinned to the coefficient and site universes so elaboration does not choose
an unrelated sheafification universe.

## New nodes

- `lem-a1-integral-pullback-signed-shift`:
  `Sheaf.Paper.IntegralPullbackSignedShift`.
- `lem-a1-integral-roos-finite-tower-realization`:
  `Sheaf.Paper.IntegralPullbackRoosFiniteTower`.
- `lem-a1-completed-integral-finite-tower-transport`:
  `Sheaf.Paper.CompletedIntegralFiniteTowerTransport`.

The existing interface node points to the new data module; the assigned theorem
node records the assembly and its actual dependencies. Every new retained
statement has its source and a natural-language proof in its docstring and node.

Change record: `coord/changes/X3-integral-completed-comparison-interface.md`.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
