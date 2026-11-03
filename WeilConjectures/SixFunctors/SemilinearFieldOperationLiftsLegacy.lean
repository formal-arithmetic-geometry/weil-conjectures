/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.SfWeilSheafComplex
public import WeilConjectures.PoincareDuality.Derived.DerivedPullbackTensorFiniteConstraints
import WeilConjectures.DeligneLaumon.IsomorphismFieldTransport

/-! # Retained legacy semilinear comparisons

Archive of the original square components and the equivalence part of the original
field-transport proof. These declarations retain the interfaces of consumers awaiting
their own route-switch repair. The native condensed module does not import this archive;
no identification of the legacy and condensed coefficient categories is asserted.
Source: the pre-route-switch proof of prop-weil-operations, steps 2--4
(blueprint: lem-pod-semilinear-field-operation-lifts).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures

-- Compatibility declarations retained for the returned-delivery importer repair.
section CompositionElaboration
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] commonStagePullbackComparison rationalDerivedPullback
  commonStageDerivedPullback Scheme.residueField

attribute [local irreducible] rationalDerivedInternalHom commonStageDerivedInternalHom

-- Retain the category wrappers used by the common-stage operation interface.
set_option allowUnsafeReducibility true in
attribute [local irreducible] Preadditive.fullSubcategory
  StageSystem.PairCategory.categoryStruct

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory

attribute [local irreducible] sfIntegralConstructible Linear.homModule
  ObjectProperty.FullSubcategory.category
  HasDerivedCategory.standard completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence

set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem

end CompositionElaboration

section EquivalenceElaboration
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Retained part of the original field-transport proof for consumers awaiting their
own coefficient-route repair. This does not identify either legacy category with the
native condensed category used by `semilinearFieldOperationLifts`.
Source: the original proof of `pod_field_transport`, steps 2--3
(blueprint: lem-pod-semilinear-field-operation-lifts).
Proof: apply isomorphismFieldTransport to the geometric Frobenius. Its prime-unit
witnesses agree by proof irrelevance with sfWeilPrimeInvertible. The finite-stage
record supplies rationalEquivalence, and the common-stage record supplies equivalence.
No tensor, Hom or compactification assertion is used by these two projections. -/
theorem pod_field_transport_legacy_equivalences
    (D₀ : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D₀.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (T₀ : Over (Spec (.of D₀.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    (sfWeilFrobeniusPullback D₀ l hl T₀ E).IsEquivalence ∧
      (sfCommonStageWeilFrobeniusPullback D₀ l hl T₀ Ω).IsEquivalence := by
  let i := fun x ↦ sfWeilPrimeInvertible D₀ l hl T₀ x
  let : ∀ x : (D₀.geometricFiber T₀).left,
      Invertible (l : (D₀.geometricFiber T₀).left.residueField x) := i
  let : (D₀.geometricFiber T₀).left.Over (Spec (.of D₀.k)) :=
    ⟨(D₀.geometricFiber T₀).hom⟩
  let : LocallyOfFiniteType ((D₀.geometricFiber T₀).left ↘ Spec (.of D₀.k)) := by
    exact inferInstanceAs (LocallyOfFiniteType
      (pullback.snd T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D₀.k₀ D₀.k)))))
  let : QuasiCompact ((D₀.geometricFiber T₀).left ↘ Spec (.of D₀.k)) := by
    exact inferInstanceAs (QuasiCompact
      (pullback.snd T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D₀.k₀ D₀.k)))))
  let : IsIso (D₀.geometricFrobenius T₀).hom := (D₀.geometricFrobenius T₀).isIso_hom
  obtain ⟨iX, iY, H⟩ := isomorphismFieldTransport D₀ l hl Ω
    (D₀.geometricFrobenius T₀).hom
  have hiX : iX = i := Subsingleton.elim _ _
  have hiY : iY = i := Subsingleton.elim _ _
  cases hiX
  cases hiY
  obtain ⟨_, _, hE, _, _, _, _, ⟨U⟩, _⟩ := H
  obtain ⟨A⟩ := (hE E).1
  exact ⟨A.rationalEquivalence, U.equivalence⟩

end EquivalenceElaboration

end WeilConjectures
