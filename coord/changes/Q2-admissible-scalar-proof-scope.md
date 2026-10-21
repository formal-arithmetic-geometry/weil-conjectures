# AlgebraicGeometry.ProEtale.AdmissibleScalarRealization.admissible_scalar_realization_exact

## Reason

The new proof uses additional namespaces, scoped notation, elaboration options, and local
irreducibility attributes. Preflight requested this record for added section commands.
All original public definitions, public imports, and theorem statements remain verbatim.
The four added private instances are explicitly local. The existing unit-route integral-limit
module remains imported. No target statement or definition changes its meaning.

## Old

Original theorem signature (unchanged):

```lean
theorem admissible_scalar_realization_exact (ℓ : ℕ) [Fact ℓ.Prime] (T : Scheme.{u}) :
    (∀ (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      [Finite A] [DiscreteTopology A],
      (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) →
      ScalarAssertions A T ∧ IsIso (FiniteDiscreteOrdinary.canonicalAbelianMap A T)) ∧
    (ScalarAssertions (ULift.{u} ℤ_[ℓ]) T ∧
      CompletedAssertions (ULift.{u} ℤ_[ℓ]) T (ℓ : ULift.{u} ℤ_[ℓ])) ∧
    (∀ (E : Type u) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E],
      IntegralAssertions ℓ E T ∧ RationalAssertions ℓ E T) ∧
    ScalarAssertions (ULift.{u} ℚ_[ℓ]) T ∧
    ScalarAssertions (ULift.{u} (PadicAlgCl ℓ)) T
```

Original section commands:

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
open FiniteConstantModel
```

## New

The theorem signature above is unchanged. Additional section commands and local options:

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
open CategoryTheory.MonObj
open scoped TensorProduct Topology
open FiniteConstantModel
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
attribute [local irreducible] constantPresheafRingMap constantRingMap
```

Added private instances `constantFunctions_locallySurjective`, `constantFunctions_locallyInjective`,
`localEquivalences`, and `sliceLocalEquivalences` use `local instance`; no new instance
registration is exported. The new public comparison theorem has its own new DAG node and module.

## Users

`tools/downstream.py Sheaf.Paper.AdmissibleScalarRealizationExact --uses localizedModel
ScalarAssertions scalarMap CompletedIdentification LocalizedFlatness CompletedAssertions
IntegralAssertions RationalAssertions admissible_scalar_realization_exact` found zero downstream
modules and only the item itself as a textual user of these declarations.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdmissibleScalarRealizationExact | Q2 | Proof replaced; public interface unchanged |
| Sheaf.Paper.CompactAdicContinuousIdentification | new in Q2 delivery | Separate comparison theorem |

Parents with unfinished proofs continue to use the same item declaration and DAG attachment.
No adaptations are necessary and no existing public declaration is withdrawn.

## Status

landed 20261021T193928-L-1326247 2026-10-21 (merge of deliver/Q2/Sheaf.Paper.AdmissibleScalarRealizationExact)
