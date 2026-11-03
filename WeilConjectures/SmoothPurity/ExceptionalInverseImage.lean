/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.FiniteExceptionalInverseImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Native.NativeConstructibleExceptionalInverseImage
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
public import Mathlib.CategoryTheory.Triangulated.Functor
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.SixFunctors.ShriekCoefficientIsomorphism
public import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
public import WeilConjectures.CategoryTheory.Brown.BrownHypothesesDefinitions
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.Compactification.Dense
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Ambient.AmbientExceptionalRightAdjoint
public import WeilConjectures.SmoothPurity.Supporting.ConstructibleIntervalsUnordered
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.AmbientCounterexampleCoproducts
public import WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginAdjointClass
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExceptionalInverseImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructiblePushforwardRestriction
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekPreservation
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekFiniteness
public import Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSupportConstructibility
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExceptionalInverseImageCurrent
public import WeilConjectures.SmoothPurity.CurrentExceptionalAdjointAdmissibility
public import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExceptionalAdjunction
public import WeilConjectures.AlgebraicGeometry.NormedCoefficientRealization.NormedCoefficientRealization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicLocalizingExceptionalBounded

/-! # Exceptional inverse image in the current field scope

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-coefficients-constructible/
sec-n-brown/sk-thm-existence/def-weil-exceptional-inverse-image.md, with Wei Yang #1412, item 18
(blueprint: def-weil-exceptional-inverse-image).

The finite operation is the existing `Scheme.finiteExceptionalInverseImage`, the canonical
realization of `ν_X^* f^× Rν_{Y,*}`. The native condensed operation below specializes the existing
single Brown construction to a finite or algebraically closed field. All preservation,
refinement, and agreement assertions are conclusions, rather than inputs to either operation.
No definition is made by selecting an arbitrary functor from a mere existence statement.

## Main definitions and statements

* `WeilConjectures.currentExceptionalInverseImage`: native Brown restriction in the current scope.
* `WeilConjectures.currentExceptionalAdjunction`: its natural Hom adjunction.
* `WeilConjectures.currentExceptionalInverseImage_properties`: exactness and uniqueness.
* `WeilConjectures.currentExceptionalInverseImage_compactification`: the recorded `i^* Rp^!`.
* `AlgebraicGeometry.ProEtale.finiteExceptionalInverseImage_current_properties`: finite clauses.
* `AlgebraicGeometry.Scheme.finiteExceptionalInverseImage_ambient_agreement`: optional agreement.

The finite definition is reused from `Sheaf.Paper.FiniteExceptionalInverseImage`. The warning
about elliptic curves is reused from `AmbientCounterexample` (bounded below) and
`AmbientCounterexampleCoproducts` (unbounded), both publicly imported here.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace WeilConjectures

/-- The finite cohomological dimension required by the native Brown construction, obtained
from precisely the field alternatives in the source, with no extra hypothesis.
Source: Wei Yang #1412, item 18 (blueprint: def-weil-exceptional-inverse-image).
Proof: split the given disjunction. In the finite-field branch install its `Finite k`
instance and apply `BaseFieldFiniteCD.of_finite`; in the algebraically closed branch install
its `IsAlgClosed k` instance and apply `BaseFieldFiniteCD.of_isAlgClosed`. -/
theorem exceptionalCurrentFieldCD (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (_hk : Finite k ∨ IsAlgClosed k) : BaseFieldFiniteCD ℓ k := by
  rcases _hk with hk | hk
  · let := hk
    exact BaseFieldFiniteCD.of_finite ℓ k
  · let := hk
    exact BaseFieldFiniteCD.of_isAlgClosed ℓ k

private theorem nativeConstructible_eq_of_iso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ') (T : Scheme.{u})
    (hctf : (constantModelBoundedConstructible Λ T ⊓ DerivedCategory.finiteTorAmplitude _) =
      constantModelBoundedConstructible Λ T)
    (heq : (constantModelBoundedConstructible Λ' T ⊓ DerivedCategory.finiteTorAmplitude _) =
      boundedConstructible (condensedRingObj Λ' T)) :
    constantModelBoundedConstructible Λ T = boundedConstructible (condensedRingObj Λ T) := by
  have : IsIso e.inv.hom := inferInstanceAs (IsIso ((Mon.forget _).map e.inv))
  funext K
  apply propext
  have hc := (shriekCoefficientIso_transport e T).2.2.2.1 K
  change (constantModelBoundedConstructible Λ' T ⊓ DerivedCategory.finiteTorAmplitude _)
      ((Mod.comap (coefficientMap e.inv.hom T)).mapDerivedCategory.obj K) ↔
    (constantModelBoundedConstructible Λ T ⊓ DerivedCategory.finiteTorAmplitude _) K at hc
  rw [hctf, heq] at hc
  exact hc.symm.trans
    (NormedCoefficientRealization.bounded_comap_iff (coefficientMap e.inv.hom T) K)

private theorem nativeConstructible_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (hΛ : IsNativeExceptionalCoefficient ℓ Λ)
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T] [IsLocallyNoetherian T]
    [TopologicalSpace.NoetherianSpace T] :
    constantModelBoundedConstructible Λ T = boundedConstructible (condensedRingObj Λ T) := by
  have ht := (localizingClosure_ctf_equals_bc ℓ T Λ hΛ).1.2.2.1
  have integral (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
      [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] :=
    (AlgebraicGeometry.ProEtale.certified_comparison _ ℓ (.integral E) T).2
  have rational (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
      [FiniteDimensional ℚ_[ℓ] E] :=
    (AlgebraicGeometry.ProEtale.certified_comparison _ ℓ (.continuous E) T).2
  unfold IsNativeExceptionalCoefficient at hΛ
  rcases hΛ with h | h | ⟨E, h | h⟩ | h
  · obtain ⟨e⟩ := h
    obtain ⟨_, _, _, _, _, _, _, _, _, z, _⟩ :=
      Profinite.base_coefficient_condensed_identification.{u} ℓ
    exact nativeConstructible_eq_of_iso (e ≪≫ z) T ht
      (integral (⊥ : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)))
  · obtain ⟨e⟩ := h
    exact nativeConstructible_eq_of_iso e T ht (rational ℚ_[ℓ])
  · obtain ⟨e⟩ := h
    exact nativeConstructible_eq_of_iso e T ht (integral E.1)
  · obtain ⟨e⟩ := h
    exact nativeConstructible_eq_of_iso e T ht (rational E.1)
  · obtain ⟨e⟩ := h
    exact nativeConstructible_eq_of_iso e T ht
      (AlgebraicGeometry.ProEtale.certified_comparison _ ℓ .algebraicClosure T).2

/-- Restrict the compactification comparison supplied by Brown existence. -/
private theorem nativeLowerShriek_comparison (c : Compactification f.left) :
    Nonempty (nativeConstructibleLowerShriek Λ ℓ k (exceptionalCurrentFieldCD ℓ k hk) f hΛ ⋙
        (constantModelBoundedConstructible Λ Y.left).ι ≅
      (constantModelBoundedConstructible Λ X.left).ι ⋙
        rightDerivedLowerShriekOfCompactification Λ c) := by
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  have eX := (localizingClosure_ctf_equals_bc ℓ X.left Λ hΛ).1.2.2.1
  obtain ⟨hX, hY, hSX, _, h, sX, sY, H⟩ :=
    exceptionalInverseImage_exists Λ ℓ k (exceptionalCurrentFieldCD ℓ k hk) f
      (nativeCoefficient_admissible Λ ℓ hΛ)
  let := hX
  let := hY
  let := sX
  let := sY
  obtain ⟨_, _, _, _, _, hc, _, _⟩ := H
  obtain ⟨e⟩ := hc c
  have iX : constantModelBoundedConstructible Λ X.left ≤
      localizingClosureProEtale Λ X.left := by rwa [eX] at hSX
  exact ⟨NatIso.ofComponents
    (fun K ↦ e.app ⟨K.obj, iX K.obj K.property⟩)
    (by intro K L a; exact e.hom.naturality ((ObjectProperty.ιOfLE iX).map a))⟩

private theorem nativeProper_hasRightAdjoint [IsProper f.left] :
    ∃ hP : ∀ K : ProEtale.BoundedConstructible (condensedRingObj Λ X.left),
        boundedConstructible (condensedRingObj Λ Y.left)
          ((lowerStar Λ f.left).rightDerivedFunctor.obj K.obj),
      ((boundedConstructible (condensedRingObj Λ Y.left)).lift
        ((boundedConstructible (condensedRingObj Λ X.left)).ι ⋙
          (lowerStar Λ f.left).rightDerivedFunctor) hP).IsLeftAdjoint := by
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  let : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  let : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  let : IsNoetherian X.left := ⟨⟩
  let : IsNoetherian Y.left := ⟨⟩
  have eX := nativeConstructible_eq Λ ℓ hΛ X.left
  have eY := nativeConstructible_eq Λ ℓ hΛ Y.left
  let JX := ObjectProperty.ιOfLE (le_of_eq eX.symm)
  let JY := ObjectProperty.ιOfLE (le_of_eq eY.symm)
  let IX := ObjectProperty.ιOfLE (le_of_eq eX)
  let F := nativeConstructibleLowerShriek Λ ℓ k (exceptionalCurrentFieldCD ℓ k hk) f hΛ
  let G := nativeConstructibleExceptionalInverseImage Λ ℓ k
    (exceptionalCurrentFieldCD ℓ k hk) f hΛ
  let eShriek : openImmersionLowerShriek Λ (𝟙 X.left) ≅ 𝟭 _ :=
    ((openImmersionLowerShriekUpperStarAdjunction Λ (𝟙 X.left)).ofNatIsoRight
      (upperStarId Λ X.left)).leftAdjointUniq Adjunction.id
  let eId := Functor.mapDerivedCategoryNatIso eShriek ≪≫
    Functor.mapDerivedCategoryIdIso _
  let ec : rightDerivedLowerShriekOfCompactification Λ
      (Compactification.ofIsProper f.left) ≅ (lowerStar Λ f.left).rightDerivedFunctor :=
    Functor.isoWhiskerRight eId _ ≪≫ Functor.leftUnitor _
  obtain ⟨beta⟩ := nativeLowerShriek_comparison Λ ℓ k hk f hΛ
    (Compactification.ofIsProper f.left)
  let e := beta ≪≫ Functor.isoWhiskerLeft _ ec
  have hP : ∀ K : ProEtale.BoundedConstructible (condensedRingObj Λ X.left),
      boundedConstructible (condensedRingObj Λ Y.left)
        ((lowerStar Λ f.left).rightDerivedFunctor.obj K.obj) := by
    intro K
    exact (boundedConstructible _).prop_of_iso (e.app (JX.obj K))
      ((le_of_eq eY) _ (F.obj (JX.obj K)).property)
  let P := (boundedConstructible (condensedRingObj Λ Y.left)).lift
    ((boundedConstructible (condensedRingObj Λ X.left)).ι ⋙
      (lowerStar Λ f.left).rightDerivedFunctor) hP
  let R := JY ⋙ G ⋙ IX
  let comm1 : JX ⋙ F ≅ P ⋙ JY :=
    NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _ (e.app (JX.obj K)))
      (by intro K L a; apply ObjectProperty.hom_ext _; exact e.hom.naturality (JX.map a))
  let comm2 : JY ⋙ G ≅ R ⋙ JX :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; simp; rfl)
  exact ⟨hP, ((nativeConstructibleExceptionalAdjunction Λ ℓ k
    (exceptionalCurrentFieldCD ℓ k hk) f hΛ).restrictFullyFaithful
      (ObjectProperty.fullyFaithfulιOfLE _) (ObjectProperty.fullyFaithfulιOfLE _)
        comm1 comm2).isLeftAdjoint⟩

private theorem nativeConstructibilityComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ : IsNativeExceptionalCoefficient ℓ Λ)
    (T : Scheme.{u}) [CompactSpace T] [IsLocallyNoetherian T] :
    boundedConstructible (condensedRingObj Λ T) = constantModelBoundedConstructible Λ T := by
  have transport {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
      [MonObj Λ'] [IsCommMonObj Λ'] (e : Mon.mk Λ ≅ Mon.mk Λ')
      (h : IsEllAdicCoefficient ℓ Λ' inferInstance) :
      boundedConstructible (condensedRingObj Λ T) =
        constantModelBoundedConstructible Λ T := by
    have hm := comparison_transport e.symm T
      (adicConstructibilityPredicateComparison ℓ T Λ' h).1
    funext K
    apply propext
    exact and_congr_right fun _ ↦ forall_congr' fun n ↦ hm _
  rcases hΛ with e | e | ⟨E, e | e⟩ | e
  · obtain ⟨_, _, _, _, _, _, _, _, _, z, _⟩ :=
      Profinite.base_coefficient_condensed_identification.{u} ℓ
    exact transport (e.some ≪≫ z) (.integral
      (⊥ : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)))
  · exact transport e.some (.continuous ℚ_[ℓ])
  · exact transport e.some (.integral E.1)
  · exact transport e.some (.continuous E.1)
  · exact transport e.some .algebraicClosure

-- Brown's comparison clause is available for every compactification, not only its choice.

private theorem nativeCompactSupportComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hk : Finite k ∨ IsAlgClosed k) {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (hΛ : IsNativeExceptionalCoefficient ℓ Λ)
    (c : Compactification f.left) :
    Nonempty ((constantModelBoundedConstructible Λ X.left).ι ⋙
        rightDerivedLowerShriekOfCompactification Λ (compactificationOverField f) ≅
      (constantModelBoundedConstructible Λ X.left).ι ⋙
        rightDerivedLowerShriekOfCompactification Λ c) := by
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  have ht : (constantModelBoundedConstructible Λ X.left ⊓
      DerivedCategory.finiteTorAmplitude _) = constantModelBoundedConstructible Λ X.left :=
    (AlgebraicGeometry.ProEtale.localizingClosure_ctf_equals_bc ℓ X.left Λ hΛ).1.2.2.1
  have ha : IsLocalizingAdmissibleCoefficient ℓ Λ := by
    rcases hΛ with h | h | ⟨E, h | h⟩ | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, h⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨E, h⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  obtain ⟨hX, hY, hSX, hSY, h, sX, sY, H⟩ :=
    exceptionalInverseImage_exists_current Λ ℓ k hk f ha
  let := hX
  let := hY
  let := sX
  let := sY
  obtain ⟨F, sF, H⟩ := H
  let := sF
  obtain ⟨eF, _, _, _, _, hc, _⟩ := H
  have iX : constantModelBoundedConstructible Λ X.left ≤
      localizingClosureProEtale Λ X.left := by
    rwa [ht] at hSX
  exact ⟨Functor.isoWhiskerLeft (ObjectProperty.ιOfLE iX)
    ((eqToIso eF).symm ≪≫ (hc c).some)⟩

-- Transfer the proper native adjunction across the equality of the two predicates.

private theorem nativeProperPushforwardAdjoint
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hk : Finite k ∨ IsAlgClosed k) {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (hΛ : IsNativeExceptionalCoefficient ℓ Λ)
    [IsProper f.left] :
    ∃ hP : ∀ K : AlgebraicGeometry.ProEtale.BoundedConstructible (condensedRingObj Λ X.left),
        boundedConstructible (condensedRingObj Λ Y.left)
          ((lowerStar Λ f.left).rightDerivedFunctor.obj K.obj),
      ((boundedConstructible (condensedRingObj Λ Y.left)).lift
        ((boundedConstructible (condensedRingObj Λ X.left)).ι ⋙
          (lowerStar Λ f.left).rightDerivedFunctor) hP).IsLeftAdjoint := by
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have eX := nativeConstructibilityComparison Λ ℓ hΛ X.left
  have eY := nativeConstructibilityComparison Λ ℓ hΛ Y.left
  let iX := ObjectProperty.ιOfLE (le_of_eq eX.symm)
  let iY := ObjectProperty.ιOfLE (le_of_eq eY.symm)
  let : iX.IsEquivalence := (ObjectProperty.isEquivalence_ιOfLE_iff _).mpr
    ((le_of_eq eX).trans (ObjectProperty.le_isoClosure _))
  let : iY.IsEquivalence := (ObjectProperty.isEquivalence_ιOfLE_iff _).mpr
    ((le_of_eq eY).trans (ObjectProperty.le_isoClosure _))
  let F := nativeConstructibleLowerShriek Λ ℓ k (exceptionalCurrentFieldCD ℓ k hk) f hΛ
  obtain ⟨ec⟩ := nativeCompactSupportComparison Λ ℓ k hk f hΛ
    (Compactification.ofIsProper f.left)
  let e : (constantModelBoundedConstructible Λ X.left).ι ⋙
        rightDerivedLowerShriekOfCompactification Λ (compactificationOverField f) ≅
      (constantModelBoundedConstructible Λ X.left).ι ⋙
        (lowerStar Λ f.left).rightDerivedFunctor :=
    ec ≪≫
      Functor.isoWhiskerLeft _
        (Functor.isoWhiskerRight (derivedOpenImmersionLowerShriekId Λ X.left) _ ≪≫
          Functor.leftUnitor _)
  have hP (K : AlgebraicGeometry.ProEtale.BoundedConstructible (condensedRingObj Λ X.left)) :
      boundedConstructible (condensedRingObj Λ Y.left)
        ((lowerStar Λ f.left).rightDerivedFunctor.obj K.obj) := by
    let K' : ConstantModelBoundedConstructible Λ X.left :=
      ⟨K.obj, (congrFun eX K.obj).mp K.property⟩
    exact (boundedConstructible (condensedRingObj Λ Y.left)).prop_of_iso (e.app K')
      ((congrFun eY _).mpr (F.obj K').property)
  let P := (boundedConstructible (condensedRingObj Λ Y.left)).lift
    ((boundedConstructible (condensedRingObj Λ X.left)).ι ⋙
      (lowerStar Λ f.left).rightDerivedFunctor) hP
  let ep : F ⋙ iY ≅ iX ⋙ P :=
    ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso e
  have : (iX ⋙ P).IsLeftAdjoint := Functor.isLeftAdjoint_of_iso ep
  exact ⟨hP, (Functor.isLeftAdjoint_comp_iff_right iX P).mp this⟩

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (hk : Finite k ∨ IsAlgClosed k)
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) (hΛ : IsNativeExceptionalCoefficient ℓ Λ)

/-- The native condensed exceptional inverse image in the current field scope. Its object and
morphism maps are those of the existing Brown right adjoint restricted to bounded constructible
objects; the field assumption supplies its finite-cd proof. It uses no finite coefficient tower.
Source: non-finite Brown paragraph and Wei Yang #1412, item 18
(blueprint: def-weil-exceptional-inverse-image). -/
def currentExceptionalInverseImage :
    ConstantModelBoundedConstructible Λ Y.left ⥤ ConstantModelBoundedConstructible Λ X.left :=
  nativeConstructibleExceptionalInverseImage Λ ℓ k (exceptionalCurrentFieldCD ℓ k hk) f hΛ

/-- The actual restricted compact-support functor with its natural Hom adjunction to the
native operation. This is the published restriction of the single localizing Brown adjunction.
Source: defining Hom bijections (blueprint: def-weil-exceptional-inverse-image). -/
def currentExceptionalAdjunction :
    nativeConstructibleLowerShriek Λ ℓ k (exceptionalCurrentFieldCD ℓ k hk) f hΛ ⊣
      currentExceptionalInverseImage Λ ℓ k hk f hΛ :=
  nativeConstructibleExceptionalAdjunction Λ ℓ k (exceptionalCurrentFieldCD ℓ k hk) f hΛ

/-- The condensed restriction is exact, comes from the single native localizing adjunction,
and agrees with every right adjoint of the same restricted compact-support functor, uniquely
when the counit is fixed. In particular this characterizes the compactification construction
`i^* Rp^!`. The finite-Tor and bounded-constructible predicates coincide at these coefficients.

Source: native Brown restriction paragraph (blueprint: def-weil-exceptional-inverse-image).
Proof, following steps 2 and 6 of the node: apply Brown existence (3) and preservation (4) to
these native coefficients on the localizing closures. The independent finite-Tor comparison
identifies Dctf with Dbc. Restrict both adjoints along the full inclusions. The inherited shift
on compact support induces the adjoint shift and exactness. A compactification composite is
right adjoint to the same compact support, so transpose its counit and use the triangle
identities to obtain the unique counit-compatible comparison. No scalar comparison enters.
-/
theorem currentExceptionalInverseImage_properties :
    ((constantModelBoundedConstructible Λ X.left ⊓ DerivedCategory.finiteTorAmplitude _) =
      constantModelBoundedConstructible Λ X.left) ∧
    ((constantModelBoundedConstructible Λ Y.left ⊓ DerivedCategory.finiteTorAmplitude _) =
      constantModelBoundedConstructible Λ Y.left) ∧
    (∃ (hX : (constantModelBoundedConstructible Λ X.left).IsTriangulated)
      (hY : (constantModelBoundedConstructible Λ Y.left).IsTriangulated),
      (fun [_triX : (constantModelBoundedConstructible Λ X.left).IsTriangulated]
          [_triY : (constantModelBoundedConstructible Λ Y.left).IsTriangulated] ↦
        ∃ s : (nativeConstructibleLowerShriek Λ ℓ k
            (exceptionalCurrentFieldCD ℓ k hk) f hΛ).CommShift ℤ,
        ∃ t : (currentExceptionalInverseImage Λ ℓ k hk f hΛ).CommShift ℤ,
          (fun [_s : (nativeConstructibleLowerShriek Λ ℓ k
              (exceptionalCurrentFieldCD ℓ k hk) f hΛ).CommShift ℤ]
              [_t : (currentExceptionalInverseImage Λ ℓ k hk f hΛ).CommShift ℤ] ↦
            (currentExceptionalAdjunction Λ ℓ k hk f hΛ).IsTriangulated)
            (_s := s) (_t := t)) (_triX := hX) (_triY := hY)) ∧
    ∀ (G : ConstantModelBoundedConstructible Λ Y.left ⥤
        ConstantModelBoundedConstructible Λ X.left)
      (adj : nativeConstructibleLowerShriek Λ ℓ k
        (exceptionalCurrentFieldCD ℓ k hk) f hΛ ⊣ G),
      ∃! e : currentExceptionalInverseImage Λ ℓ k hk f hΛ ≅ G,
        ∀ L, (nativeConstructibleLowerShriek Λ ℓ k
          (exceptionalCurrentFieldCD ℓ k hk) f hΛ).map (e.hom.app L) ≫ adj.counit.app L =
            (currentExceptionalAdjunction Λ ℓ k hk f hΛ).counit.app L := by
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  let : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  let : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  refine ⟨(localizingClosure_ctf_equals_bc ℓ X.left Λ hΛ).1.2.2.1,
    (localizingClosure_ctf_equals_bc ℓ Y.left Λ hΛ).1.2.2.1, ?_, ?_⟩
  · exact nativeConstructibleExceptionalAdjunction_exact Λ ℓ k
      (exceptionalCurrentFieldCD ℓ k hk) f hΛ
  · intro G adj
    exact nativeConstructibleExceptionalInverseImage_unique Λ ℓ k
      (exceptionalCurrentFieldCD ℓ k hk) f hΛ G adj

/-- Agreement with the dependency's actual compactification composite, through the canonical
full inclusions of constant-model constructible objects into native bounded constructible
objects. The preservation and proper-adjoint witnesses are conclusions, not hypotheses.
Source: non-finite compactification agreement paragraph
(blueprint: def-weil-exceptional-inverse-image).
Proof: native constructibility agrees with constant finite local models for the specified
adic coefficients. Proper pushforward preserves them. Brown representability for the proper
leg supplies its restricted right adjoint. The open adjunction composes with the proper
adjunction to give precisely `boundedConstructibleExceptionalAdjunction`. Both left adjoints
are the restriction of the canonical compact-support functor, compared by the canonical
compactification independence map. Counit-compatible uniqueness of right adjoints yields
the displayed isomorphism after the full inclusions. -/
theorem currentExceptionalInverseImage_compactification :
    ∃ hP : ∀ K : AlgebraicGeometry.ProEtale.BoundedConstructible
        (condensedRingObj Λ (exceptionalInverseImageCompactification f).Z),
      boundedConstructible (condensedRingObj Λ Y.left)
        ((lowerStar Λ (exceptionalInverseImageCompactification f).g).rightDerivedFunctor.obj
          K.obj),
    ∃ _hAdj : (exceptionalInverseImageProperPushforward Λ f hP).IsLeftAdjoint,
    ∃ (hX : constantModelBoundedConstructible Λ X.left ≤
        boundedConstructible (condensedRingObj Λ X.left))
      (hY : constantModelBoundedConstructible Λ Y.left ≤
        boundedConstructible (condensedRingObj Λ Y.left)),
      letI := _hAdj
      Nonempty (currentExceptionalInverseImage Λ ℓ k hk f hΛ ⋙ ObjectProperty.ιOfLE hX ≅
        ObjectProperty.ιOfLE hY ⋙ boundedConstructibleUpperShriekOfRightAdjoint Λ ℓ f hP) := by
  classical
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  let : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  let : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  let : IsNoetherian X.left := ⟨⟩
  let : IsNoetherian Y.left := ⟨⟩
  have eX := nativeConstructible_eq Λ ℓ hΛ X.left
  have eY := nativeConstructible_eq Λ ℓ hΛ Y.left
  let c := exceptionalInverseImageCompactification f
  obtain ⟨hP, hAdj⟩ := nativeProper_hasRightAdjoint Λ ℓ k hk c.overG hΛ
  let : (exceptionalInverseImageProperPushforward Λ f hP).IsLeftAdjoint := hAdj
  refine ⟨hP, hAdj, le_of_eq eX, le_of_eq eY, ?_⟩
  let JX := ObjectProperty.ιOfLE (le_of_eq eX)
  let JY := ObjectProperty.ιOfLE (le_of_eq eY)
  let IX := ObjectProperty.ιOfLE (le_of_eq eX.symm)
  let Fi := boundedConstructibleOpenImmersionLowerShriek Λ ℓ c.overI
  let P := exceptionalInverseImageProperPushforward Λ f hP
  let F := Fi ⋙ P
  let R := boundedConstructibleUpperShriekOfRightAdjoint Λ ℓ f hP
  let adj : F ⊣ R :=
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ c.overI).comp
      (Adjunction.ofIsLeftAdjoint P)
  let ep : P ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ (lowerStar Λ c.g).rightDerivedFunctor := Iso.refl _
  let compCompat : F ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ rightDerivedLowerShriekOfCompactification Λ c :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft Fi ep ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (boundedConstructibleOpenImmersionLowerShriekCompatibility Λ ℓ c.overI) _ ≪≫
      Functor.associator _ _ _
  obtain ⟨beta⟩ := nativeLowerShriek_comparison Λ ℓ k hk f hΛ c
  let Fn := nativeConstructibleLowerShriek Λ ℓ k (exceptionalCurrentFieldCD ℓ k hk) f hΛ
  let G := JY ⋙ R ⋙ IX
  let gamma : (JX ⋙ F) ⋙ (boundedConstructible _).ι ≅
      (Fn ⋙ JY) ⋙ (boundedConstructible _).ι :=
    Functor.isoWhiskerLeft JX compCompat ≪≫ beta.symm
  let comm1 : JX ⋙ F ≅ Fn ⋙ JY :=
    ((boundedConstructible _).fullyFaithfulι.whiskeringRight _).preimageIso gamma
  let comm2 : JY ⋙ R ≅ G ⋙ JX :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; simp; rfl)
  let adjG : Fn ⊣ G := adj.restrictFullyFaithful
    (ObjectProperty.fullyFaithfulιOfLE _) (ObjectProperty.fullyFaithfulιOfLE _) comm1 comm2
  exact ⟨Functor.isoWhiskerRight
    ((currentExceptionalAdjunction Λ ℓ k hk f hΛ).rightAdjointUniq adjG) JX⟩

end WeilConjectures

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
