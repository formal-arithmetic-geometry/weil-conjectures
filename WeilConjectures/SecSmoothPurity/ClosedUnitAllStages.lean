/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import WeilConjectures.AlgebraicGeometry.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.SfDerivedComplete
public import WeilConjectures.AlgebraicGeometry.SfRationalizationKaroubi
public import WeilConjectures.AlgebraicGeometry.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.AlgebraicGeometry.SfDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.SfIntegralReductionTowerSupplement
public import WeilConjectures.AlgebraicGeometry.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.ProEtaleRingedOpenClosed
import WeilConjectures.AlgebraicGeometry.ProEtaleIntrinsicClosedAmbient
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantRingOperations
import all WeilConjectures.AlgebraicGeometry.SfCompleteDirectImageReduction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import all WeilConjectures.AlgebraicGeometry.SfIntegralDirectImageConstructible
import WeilConjectures.AlgebraicGeometry.SfStrictDirectImageIntegralModels
import WeilConjectures.AlgebraicGeometry.SfStrictDirectImageIntegralComparisons
import WeilConjectures.AlgebraicGeometry.SfStrictDirectImageRationalComparisons
import all WeilConjectures.CategoryTheory.StageSystemTargetComparison
import all WeilConjectures.AlgebraicGeometry.SfCommonStageFullFaithfulness
import WeilConjectures.CategoryTheory.ScalarLocalizationNaturalIso

/-!
# Closed direct image is fully faithful at every coefficient stage

Source: Weil blueprint, sec-smooth-purity/sk-prop-sf-closed-unit,
prop-sf-closed-unit-all-stages, order 1861
(blueprint: prop-sf-closed-unit-all-stages).

The conclusion includes existence of the restricted functors. The comparison squares
identify their object and morphism maps with the recorded ambient direct images and
with scalar localization. At algebraically closed coefficients the comparison is on
every finite-field inclusion, with the scalar cocycle and change-of-stage equations,
hence on every common-stage representative.
No direct-image functor is an unconstrained hypothesis.
-/

@[expose] public section
set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry

namespace WeilConjectures

/-- A presentation of the restrictions of the specified direct image at a fixed
finite coefficient extension. The finite and integral squares are comparisons with
the recorded ambient functors, not merely assertions of their source and target.
The rational square and localized linearity specify scalar localization of the
integral restriction, including its action on every tensor Hom group. Presentations
are allowed up to natural isomorphism, as are the derived functors themselves.

Source: Weil blueprint, order 1861, finite, integral and rational stages
(blueprint: prop-sf-closed-unit-all-stages). -/
structure ClosedDirectImageCoefficientStages
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {Z X : Scheme.{u}} (i : Z ⟶ X) where
  /-- The finite-level restriction, at every positive exponent. -/
  finiteStar : ∀ (n : ℕ) (hn : 1 ≤ n),
    (Scheme.intrinsicFiniteTorsionConstructible l E n hn Z).FullSubcategory ⥤
      (Scheme.intrinsicFiniteTorsionConstructible l E n hn X).FullSubcategory
  /-- The finite functor is the restriction of the actual derived image along i. -/
  finiteComparison : ∀ (n : ℕ) (hn : 1 ≤ n),
    finiteStar n hn ⋙ (Scheme.intrinsicFiniteTorsionConstructible l E n hn X).ι ≅
      (Scheme.intrinsicFiniteTorsionConstructible l E n hn Z).ι ⋙
        Scheme.proEtaleConstantDerivedDirectImage i (Padic.coefficientExtensionRing l E n)
  /-- The integral restriction. -/
  integralStar : sfIntegralConstructibleCategory l E Z ⥤ sfIntegralConstructibleCategory l E X
  /-- Its ambient realization is the specified completed-coefficient derived image. -/
  integralComparison : integralStar ⋙ (sfIntegralConstructible l E X).ι ≅
    (sfIntegralConstructible l E Z).ι ⋙ sfCompletedDerivedDirectImage l E i
  /-- The raw rationalization of the integral restriction. -/
  rationalStar : sfRationalConstructibleCategory l E Z ⥤ sfRationalConstructibleCategory l E X
  /-- Additivity is needed to specify the action on arbitrary sums of pure tensors. -/
  rationalAdditive : rationalStar.Additive
  /-- The scalar factor is fixed, so a scalar-twisting functor is not allowed. -/
  rationalLinear : rationalStar.Linear
    (Localization.Away (Padic.coefficientExtensionUniformizer l E))
  /-- On integral generators the rational functor is precisely the integral image. -/
  rationalComparison : sfRationalConstructibleLocalization l E Z ⋙ rationalStar ≅
    integralStar ⋙ sfRationalConstructibleLocalization l E X

/-- Compatible presentations of the actual direct image at every coefficient field
and on the common-stage category. Each inclusion comparison is natural in every
finite-stage morphism. The scalar cocycle and the inclusion coherence fix its
compatibility with all canonical changes of stage.
Source: Weil blueprint, order 1861, algebraically closed stage
(blueprint: prop-sf-closed-unit-all-stages). -/
structure ClosedDirectImageStages
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {Z X : Scheme.{u}} (i : Z ⟶ X) where
  /-- Restrictions of the actual ambient direct images, with their scalar localization. -/
  coefficient : ∀ (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E], ClosedDirectImageCoefficientStages l E i
  /-- The direct-image comparisons with the recorded finite scalar transitions. -/
  scalarComparison : ∀ {E L : AlgebraicallyClosedCoefficients.Index l Ω} (h : E ≤ L),
    (coefficient (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)).rationalStar ⋙
        (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h ≅
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Z).T h ⋙
        (coefficient (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)).rationalStar
  /-- Pasting successive extensions agrees with their direct comparison. -/
  scalarCoherence : ∀ {E L M : AlgebraicallyClosedCoefficients.Index l Ω}
    (h : E ≤ L) (h' : L ≤ M)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Z E),
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h').map
        ((scalarComparison h).hom.app K) ≫
      (scalarComparison h').hom.app
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Z).T h).obj K) ≫
      (coefficient (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω M)).rationalStar.map
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Z).assoc h h').hom.app K) =
      ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).assoc h h').hom.app
          ((coefficient (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)).rationalStar.obj
            K) ≫
        (scalarComparison (h.trans h')).hom.app K
  /-- The common-stage realization. -/
  algebraicallyClosedStar : generalAlgebraicallyClosedConstructibleCategory l Ω Z ⥤
    generalAlgebraicallyClosedConstructibleCategory l Ω X
  /-- On each finite-field inclusion this is the rationalized direct image along i. -/
  inclusionComparison : ∀ E : AlgebraicallyClosedCoefficients.Index l Ω,
    GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := Z) E ⋙
        algebraicallyClosedStar ≅
      (coefficient (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)).rationalStar ⋙
        GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) E
  /-- The inclusion comparisons respect the canonical change-of-stage arrows. -/
  inclusionCoherence : ∀ {E L : AlgebraicallyClosedCoefficients.Index l Ω} (h : E ≤ L)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Z E),
    algebraicallyClosedStar.map
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Z).transIso h).hom.app K) ≫
      (inclusionComparison E).hom.app K =
      (inclusionComparison L).hom.app
          (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Z).T h).obj K) ≫
        (GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) L).map
          ((scalarComparison h).inv.app K) ≫
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).transIso h).hom.app
          ((coefficient (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)).rationalStar.obj
            K)


attribute [-instance] CompletedCoefficientPushforward.modAbelian
  CompletedCoefficientPushforward.hasDerived in
private theorem closed_ring_fullyFaithful
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ)
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (T : Sheaf (Scheme.ProEt.topology Z) CommRingCat.{u + 1})
    (c : (Scheme.proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R ≅ T) :
    (Scheme.proEtaleRingDerivedDirectImage i R T c).Full ∧
      (Scheme.proEtaleRingDerivedDirectImage i R T c).Faithful := by
  obtain ⟨q, hq, ai, aj, hc, rest⟩ :=
    Scheme.proEtale_ringed_open_closed i U hU R
  have : IsIso ai.counit := NatIso.isIso_of_isIso_app _
  have : (Scheme.proEtaleRingedDirectImage i R).Full :=
    ai.fullyFaithfulROfIsIsoCounit.full
  have : (Scheme.proEtaleRingedDirectImage i R).Faithful :=
    ai.fullyFaithfulROfIsIsoCounit.faithful
  let e := Scheme.proEtaleScalarEquivalence Z
    ((sheafCompose (Scheme.ProEt.topology Z)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c)
  let d : e.functor ⋙ Scheme.proEtaleRingedDirectImage i R ≅
      Scheme.proEtaleRingModuleDirectImage i R T c := by
    refine NatIso.ofComponents (fun M ↦ ?_) ?_
    · apply (SheafOfModules.fullyFaithfulForget _).preimageIso
      exact PresheafOfModules.isoMk (fun W ↦ Iso.refl _) (by intros; rfl)
    · intro M N a
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro W
      rfl
  have : (Scheme.proEtaleRingModuleDirectImage i R T c).Full := Functor.Full.of_iso d
  have : (Scheme.proEtaleRingModuleDirectImage i R T c).Faithful :=
    Functor.Faithful.of_iso d
  have := (Scheme.proEtaleRingModuleAdjunction i R T c).preservesKInjectiveComplexes
  exact ⟨inferInstance, inferInstance⟩

private theorem closed_finite_preserves
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime] (hl : IsUnit (l : k))
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {Z X : Scheme.{u}} [Z.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (i : Z ⟶ X) [i.IsOver (Spec (.of k))] (n : ℕ) (hn : 1 ≤ n)
    (K : (Scheme.intrinsicFiniteTorsionConstructible l E n hn Z).FullSubcategory) :
    Scheme.intrinsicFiniteTorsionConstructible l E n hn X
      ((Scheme.proEtaleConstantDerivedDirectImage i
        (Padic.coefficientExtensionRing l E n)).obj K.obj) := by
  let := Padic.finite_coefficientExtensionRing l E n hn
  obtain ⟨a, ha⟩ := K.property.1.bddBelow
  obtain ⟨b, hb⟩ := K.property.1.bddAbove
  exact finite_image_constructible k (Padic.coefficientExtensionRing l E n)
    (l ^ n) (pow_pos (Fact.out : l.Prime).pos n) (coefficient_killed l E n)
    (by simpa only [Nat.cast_pow] using hl.pow n)
    (Z ↘ Spec (.of k)) (X ↘ Spec (.of k)) i (by simp) K.obj K.property.2
    (min a b) (max a b) min_le_max (by
      intro q hq
      by_contra hz
      have hlo := ha hz
      have hhi := hb hz
      rcases hq with hq | hq <;> omega)

private noncomputable def closed_coefficient_presentation
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {Z X : Scheme.{u}} (i : Z ⟶ X)
    (I : SfStrictDirectImageScalar.IntegralModel l E i)
    (h : ∀ n hn (K : (Scheme.intrinsicFiniteTorsionConstructible l E n hn Z).FullSubcategory),
      Scheme.intrinsicFiniteTorsionConstructible l E n hn X
        ((Scheme.proEtaleConstantDerivedDirectImage i
          (Padic.coefficientExtensionRing l E n)).obj K.obj)) :
    ClosedDirectImageCoefficientStages l E i where
  finiteStar n hn := (Scheme.intrinsicFiniteTorsionConstructible l E n hn X).lift
    ((Scheme.intrinsicFiniteTorsionConstructible l E n hn Z).ι ⋙
      Scheme.proEtaleConstantDerivedDirectImage i (Padic.coefficientExtensionRing l E n))
    (h n hn)
  finiteComparison n hn := Iso.refl _
  integralStar := I.image
  integralComparison := I.reconstruction.symm
  rationalStar := ScalarLocalization.transport (Padic.coefficientExtensionIntegers l E)
    (Padic.coefficientExtensionUniformizer l E) I.image
  rationalAdditive := inferInstance
  rationalLinear := inferInstance
  rationalComparison := NatIso.ofComponents (fun K ↦ Iso.refl _) (by
    intro K L f
    simp [sfRationalConstructibleLocalization, ScalarLocalization.transport,
      ScalarLocalization.transportHom, ScalarLocalization.localization])

private theorem constant_direct_image_eq
    {Z X : Scheme.{u}} (i : Z ⟶ X) (A : Type u) [CommRing A] :
    Scheme.proEtaleRingModuleDirectImage i (Scheme.proEtaleConstantRing X A)
      (Scheme.proEtaleConstantRing Z A) (Scheme.proEtaleConstantRingComparison i A) =
        Scheme.proEtaleConstantModuleDirectImage i A := by
  have h : Scheme.proEtaleRingDirectImageMap i (Scheme.proEtaleConstantRing X A)
      (Scheme.proEtaleConstantRing Z A) (Scheme.proEtaleConstantRingComparison i A) =
        Scheme.proEtaleCoefficientDirectImageMap i A := by
    change ((Scheme.proEtaleSheafAdjunction i CommRingCat.{u + 1}).homEquiv _ _)
      (((Scheme.proEtaleSheafAdjunction i CommRingCat.{u + 1}).homEquiv _ _).symm
        (Scheme.proEtaleCoefficientDirectImageMap i A)) = _
    exact Equiv.apply_symm_apply _ _
  unfold Scheme.proEtaleRingModuleDirectImage Scheme.proEtaleConstantModuleDirectImage
  rw [h]

attribute [-instance] CompletedCoefficientPushforward.modAbelian
  CompletedCoefficientPushforward.hasDerived in
private theorem closed_constant_fullyFaithful
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ) (A : Type u) [CommRing A] :
    (Scheme.proEtaleConstantDerivedDirectImage i A).Full ∧
      (Scheme.proEtaleConstantDerivedDirectImage i A).Faithful := by
  have h := closed_ring_fullyFaithful i U hU (Scheme.proEtaleConstantRing X A)
    (Scheme.proEtaleConstantRing Z A) (Scheme.proEtaleConstantRingComparison i A)
  change (Scheme.proEtaleConstantModuleDirectImage i A).rightDerivedFunctor.Full ∧
    (Scheme.proEtaleConstantModuleDirectImage i A).rightDerivedFunctor.Faithful
  have := h.1
  have := h.2
  let e := Functor.rightDerivedFunctorNatIso (eqToIso (constant_direct_image_eq i A))
  exact ⟨Functor.Full.of_iso e, Functor.Faithful.of_iso e⟩

attribute [-instance] CompletedCoefficientPushforward.modAbelian
  CompletedCoefficientPushforward.hasDerived in
private theorem closed_completed_fullyFaithful
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ) :
    (sfCompletedDerivedDirectImage l E i).Full ∧
      (sfCompletedDerivedDirectImage l E i).Faithful := by
  have h := closed_ring_fullyFaithful i U hU
    (completedIntegralCommRingSheafUnrestricted l E X)
    (completedIntegralCommRingSheafUnrestricted l E Z) (coefficient_inverse_image_iso l E i)
  change (sfCompletedModuleDirectImage l E i).rightDerivedFunctor.Full ∧
    (sfCompletedModuleDirectImage l E i).rightDerivedFunctor.Faithful
  have := h.1
  have := h.2
  let e := Functor.rightDerivedFunctorNatIso (eqToIso (completed_direct_image_eq l E i))
  exact ⟨Functor.Full.of_iso e, Functor.Faithful.of_iso e⟩

private theorem restriction_fullyFaithful
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (F : A ⥤ B) (J : B ⥤ D) [J.Faithful] (I : A ⥤ C) [I.Full] [I.Faithful]
    (G : C ⥤ D) [G.Full] [G.Faithful] (e : F ⋙ J ≅ I ⋙ G) :
    F.Full ∧ F.Faithful :=
  ⟨Functor.Full.of_comp_faithful_iso e, Functor.Faithful.of_comp_iso e⟩

private theorem localized_fullyFaithful
    (R : Type*) [CommRing R] (p : R)
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    [Linear R A] [Linear R B] (F : A ⥤ B) [F.Additive] [F.Linear R]
    [F.Full] [F.Faithful] :
    (ScalarLocalization.transport R p F).Full ∧
      (ScalarLocalization.transport R p F).Faithful := by
  have hb (K L : ScalarLocalization R A p) :
      Function.Bijective ((ScalarLocalization.transport R p F).map : (K ⟶ L) → _) := by
    let e := LinearEquiv.ofBijective (F.mapLinearMap R (X := K.obj) (Y := L.obj))
      ⟨F.map_injective, F.map_surjective⟩
    exact (e.baseChange R (Localization.Away p)).bijective
  exact ⟨⟨fun {K L} ↦ (hb K L).2⟩, ⟨fun {K L} ↦ (hb K L).1⟩⟩

private def cast_stage_morphism
    {J : Type*} [Preorder J]
    {A B : J → Type*} [∀ j, Category (A j)] [∀ j, Category (B j)]
    {S S' : StageSystem A} {T T' : StageSystem B}
    (eS : S = S') (eT : T = T') (F : S.Morphism T) : S'.Morphism T' where
  Φ := F.Φ
  β := by cases eS; cases eT; exact F.β
  coh := by cases eS; cases eT; exact F.coh

private theorem morphism_inclusion_coherence
    {J : Type*} [Preorder J] [IsDirectedOrder J]
    {A B : J → Type*} [∀ j, Category (A j)] [∀ j, Category (B j)]
    {T : StageSystem A} {V : StageSystem B} (F : T.Morphism V)
    {j k} (h : j ≤ k) (P : A j) :
    F.functor.map ((T.transIso h).hom.app P) ≫
        (F.ιCompFunctorIso j).hom.app P =
      (F.ιCompFunctorIso k).hom.app ((T.T h).obj P) ≫
        (V.ι k).map ((F.β h).inv.app P) ≫
          (V.transIso h).hom.app ((F.Φ j).obj P) := by
  simp only [StageSystem.Morphism.ιCompFunctorIso_hom_app]
  erw [Category.comp_id, Category.id_comp]
  apply (cancel_mono (F.functor.map ((T.transIso h).inv.app P))).1
  simp only [Category.assoc, ← F.functor.map_comp, Iso.hom_inv_id_app, F.functor.map_id]
  rw [← CategoryTheory.StageSystem.morphism_transition F h P, ← Functor.map_comp,
    Iso.inv_hom_id_app]
  exact ((V.ι k).map_id _).symm

/--
The finite, integral, rational, and algebraically closed restriction data exist.

The construction follows the six-step proof of the parent proposition: closed support,
finite-level recollement, completed coefficient comparison, scalar localization, and
coherent common-stage descent.  The same construction supplies all comparison squares.
Source: Weil blueprint, sec-smooth-purity/sk-prop-sf-closed-unit,
prop-sf-closed-unit-all-stages, order 1861.
(blueprint: prop-sf-closed-unit-all-stages).
-/
theorem closedUnitAllStages_exists
    (k : Type u) [Field k]
    (l : ℕ) [Fact l.Prime] (hℓ : IsUnit (l : k))
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {Z X : Scheme.{u}} [Z.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))] [LocallyOfFiniteType (Z ↘ Spec (.of k))]
    [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (i : Z ⟶ X) [i.IsOver (Spec (.of k))] [IsClosedImmersion i] :
    Nonempty (ClosedDirectImageStages l Ω i) := by
  classical
  let I : ∀ (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E], SfStrictDirectImageScalar.IntegralModel l E i :=
    fun E _ _ _ ↦ (SfStrictDirectImageScalar.strictDirectImageIntegralModel
      l E k hℓ i).some
  let C : ∀ (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E], ClosedDirectImageCoefficientStages l E i :=
    fun E _ _ _ ↦ closed_coefficient_presentation l E i (I E)
      (closed_finite_preserves k l hℓ E i)
  obtain ⟨A, c, hD, hc⟩ := SfStrictDirectImageScalar.strictDirectImageIntegralComparisons
    l Ω k hℓ i (fun E ↦ I (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E))
  let D : SfStrictDirectImageScalar.IntegralComparisons l Ω i :=
    ⟨A, fun E ↦ I (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E), c⟩
  obtain ⟨R, hr, hR⟩ :=
    SfStrictDirectImageScalar.strictDirectImageRationalComparisons l Ω i D hD hc
  rcases R with @⟨R, ha, hs, loc, theta⟩
  have he : R = fun E ↦
      (C (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)).rationalStar :=
    funext hr
  subst R
  let T (Y : Scheme.{u}) : StageSystem
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y) := {
    T := fun {E L} h ↦ GeneralAlgebraicallyClosedCoefficients.transition l Ω Y E L h
    assoc := fun {E L M} h j ↦
      GeneralAlgebraicallyClosedCoefficients.associator l Ω Y E L M h j
    cocycle := by
      intro E L M N h j m K
      exact GeneralAlgebraicallyClosedCoefficients.associator_cocycle
        l Ω Y E L M N h j m K }
  have hT (Y : Scheme.{u}) : T Y =
      GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y := by
    apply (GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique l Ω Y).unique
    · exact ⟨fun _ _ _ ↦ rfl, fun _ _ _ _ _ ↦ HEq.rfl⟩
    · exact (GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique
        l Ω Y).exists.choose_spec
  let F₀ : (T Z).Morphism (T X) := {
    Φ := fun E ↦ (C (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)).rationalStar
    β := fun {E L} h ↦ (theta E L h).symm
    coh := by
      intro E L M h j K
      have ht := hR.2.2.2.2.2.2.2 E L M h j K
      apply (cancel_epi ((theta L M j).hom.app
        ((GeneralAlgebraicallyClosedCoefficients.transition l Ω Z E L h).obj K) ≫
        (GeneralAlgebraicallyClosedCoefficients.transition l Ω X L M j).map
          ((theta E L h).hom.app K))).1
      apply (cancel_mono ((theta E M (h.trans j)).hom.app K)).1
      simpa [T, Category.assoc, ← Functor.map_comp_assoc] using ht.symm }
  let F := cast_stage_morphism (hT Z) (hT X) F₀
  refine ⟨{
    coefficient := fun E _ _ _ ↦ C E
    scalarComparison := F.β
    scalarCoherence := F.coh
    algebraicallyClosedStar := F.functor
    inclusionComparison := F.ιCompFunctorIso
    inclusionCoherence := ?_ }⟩
  exact morphism_inclusion_coherence F


attribute [-instance] CompletedCoefficientPushforward.modAbelian
  CompletedCoefficientPushforward.hasDerived in
private noncomputable def stage_presentation_iso
    {J : Type*} [Preorder J] [IsDirectedOrder J]
    {A B : J → Type*} [∀ j, Category (A j)] [∀ j, Category (B j)]
    {T : StageSystem A} {V : StageSystem B}
    (F : T.Morphism V) (G : T.PairCategory ⥤ V.PairCategory)
    (a : ∀ j, T.ι j ⋙ G ≅ F.Φ j ⋙ V.ι j)
    (ha : ∀ {j k} (h : j ≤ k) (P : A j),
      G.map ((T.transIso h).hom.app P) ≫ (a j).hom.app P =
        (a k).hom.app ((T.T h).obj P) ≫
          (V.ι k).map ((F.β h).inv.app P) ≫
            (V.transIso h).hom.app ((F.Φ j).obj P)) :
    G ≅ F.functor := by
  have hb {j k} (h : j ≤ k) (P : A j) :
      G.map ((T.transIso h).inv.app P) ≫ (a k).hom.app ((T.T h).obj P) =
        (a j).hom.app P ≫ F.functor.map ((T.transIso h).inv.app P) := by
    apply (Iso.cancel_iso_hom_left (G.mapIso ((T.transIso h).app P)) _ _).1
    dsimp only [Functor.mapIso_hom, Iso.app_hom]
    simp only [← G.map_comp_assoc, Iso.hom_inv_id_app, G.map_id, Category.id_comp]
    rw [← Category.assoc, ha, Category.assoc, Category.assoc,
      ← CategoryTheory.StageSystem.morphism_transition F h P, ← Functor.map_comp,
      Iso.inv_hom_id_app]
    erw [(V.ι k).map_id, Category.comp_id]
  refine NatIso.ofComponents (fun P ↦ (a P.stage).app P.obj) ?_
  intro P Q f
  rcases P with ⟨j, P⟩
  rcases Q with ⟨k, Q⟩
  change G.map f ≫ (a k).hom.app Q = (a j).hom.app P ≫ F.functor.map f
  induction f using StageSystem.PairCategory.hom_induction with
  | h n hP hQ u =>
    rw [StageSystem.mkHom_eq_isoToStage hP hQ u]
    apply (Iso.cancel_iso_hom_right _ _
      (F.functor.mapIso (T.isoToStage ⟨k, Q⟩ hQ))).1
    dsimp only [Functor.mapIso_hom]
    simp only [Functor.map_comp, Category.assoc, Iso.map_inv_hom_id, Category.comp_id]
    have hq := hb hQ Q
    change G.map (T.isoToStage ⟨k, Q⟩ hQ).hom ≫
      (a n).hom.app ((T.T hQ).obj Q) =
        (a k).hom.app Q ≫ F.functor.map (T.isoToStage ⟨k, Q⟩ hQ).hom at hq
    rw [← hq]
    simp only [← G.map_comp_assoc, Iso.inv_hom_id, G.map_id, Category.id_comp]
    rw [G.map_comp, Category.assoc]
    have hn := (a n).hom.naturality u
    change G.map ((T.ι n).map u) ≫ (a n).hom.app _ =
      (a n).hom.app _ ≫ (V.ι n).map ((F.Φ n).map u) at hn
    rw [hn, ← Category.assoc]
    have hp := hb hP P
    change G.map (T.isoToStage ⟨j, P⟩ hP).hom ≫
      (a n).hom.app ((T.T hP).obj P) =
        (a j).hom.app P ≫ F.functor.map (T.isoToStage ⟨j, P⟩ hP).hom at hp
    rw [hp, Category.assoc, F.functor_map_ι]

attribute [-instance] CompletedCoefficientPushforward.modAbelian
  CompletedCoefficientPushforward.hasDerived in
/--
Every presented system of closed direct-image restrictions is fully faithful at all
coefficient stages, and every available right-adjoint unit is invertible.

The proof is the Hom argument in the parent proposition: recollement gives finite
full faithfulness, Roos comparison gives integral full faithfulness, scalar localization
and common-stage coherence give the remaining stages, and Yoneda turns full faithfulness
into invertibility of each adjunction unit.  The finite ambient right adjoint comes from
closed support.  This is a strict component of the parent conclusion.
Source: Weil blueprint, sec-smooth-purity/sk-prop-sf-closed-unit,
prop-sf-closed-unit-all-stages, order 1861.
(blueprint: prop-sf-closed-unit-all-stages).
-/
theorem closedUnitAllStages_properties
    (k : Type u) [Field k]
    (l : ℕ) [Fact l.Prime] (hℓ : IsUnit (l : k))
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {Z X : Scheme.{u}} [Z.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))] [LocallyOfFiniteType (Z ↘ Spec (.of k))]
    [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (i : Z ⟶ X) [i.IsOver (Spec (.of k))] [IsClosedImmersion i]
    (S : ClosedDirectImageStages l Ω i) :
      (∀ (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E],
        (∀ (n : ℕ) (hn : 1 ≤ n),
          ((S.coefficient E).finiteStar n hn).Full ∧
            ((S.coefficient E).finiteStar n hn).Faithful) ∧
        ((S.coefficient E).integralStar.Full ∧
          (S.coefficient E).integralStar.Faithful) ∧
        ((S.coefficient E).rationalStar.Full ∧
          (S.coefficient E).rationalStar.Faithful) ∧
        (∀ (n : ℕ) (hn : 1 ≤ n)
          (G : (Scheme.intrinsicFiniteTorsionConstructible l E n hn X).FullSubcategory ⥤
            (Scheme.intrinsicFiniteTorsionConstructible l E n hn Z).FullSubcategory)
          (adj : (S.coefficient E).finiteStar n hn ⊣ G), ∀ Q, IsIso (adj.unit.app Q)) ∧
        (∀ (G : sfIntegralConstructibleCategory l E X ⥤
            sfIntegralConstructibleCategory l E Z)
          (adj : (S.coefficient E).integralStar ⊣ G), ∀ Q, IsIso (adj.unit.app Q)) ∧
        (∀ (G : sfRationalConstructibleCategory l E X ⥤
            sfRationalConstructibleCategory l E Z)
          (adj : (S.coefficient E).rationalStar ⊣ G), ∀ Q, IsIso (adj.unit.app Q)) ∧
        (∀ (n : ℕ) (_hn : 1 ≤ n),
          ∃ G : Scheme.proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n) ⥤
              Scheme.proEtaleDerivedCategory Z (Padic.coefficientExtensionRing l E n),
          ∃ adj : Scheme.proEtaleConstantDerivedDirectImage i
              (Padic.coefficientExtensionRing l E n) ⊣ G,
            ∀ Q, IsIso (adj.unit.app Q))) ∧
      (S.algebraicallyClosedStar.Full ∧ S.algebraicallyClosedStar.Faithful) ∧
      (∀ (G : generalAlgebraicallyClosedConstructibleCategory l Ω X ⥤
          generalAlgebraicallyClosedConstructibleCategory l Ω Z)
        (adj : S.algebraicallyClosedStar ⊣ G), ∀ Q, IsIso (adj.unit.app Q)) := by
  classical
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  let O : X.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let U : X.ProEt := Scheme.ProEt.mk O.ι
  have : IsOpenImmersion U.hom := inferInstanceAs (IsOpenImmersion O.ι)
  have : QuasiCompact U.hom := inferInstanceAs (QuasiCompact O.ι)
  have hU : Set.range U.hom = (Set.range i)ᶜ := by
    exact Subtype.range_coe
  have hf (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) :
      ((S.coefficient E).finiteStar n hn).Full ∧
        ((S.coefficient E).finiteStar n hn).Faithful := by
    obtain ⟨hfull, hfaithful⟩ := closed_constant_fullyFaithful i U hU
      (Padic.coefficientExtensionRing l E n)
    exact restriction_fullyFaithful _ _
      (Scheme.intrinsicFiniteTorsionConstructible l E n hn Z).ι _
      ((S.coefficient E).finiteComparison n hn)
  have hi (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E] :
      (S.coefficient E).integralStar.Full ∧ (S.coefficient E).integralStar.Faithful := by
    obtain ⟨hfull, hfaithful⟩ := closed_completed_fullyFaithful l E i U hU
    exact restriction_fullyFaithful _ _ (sfIntegralConstructible l E Z).ι _
      (S.coefficient E).integralComparison
  have hr (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E] :
      (S.coefficient E).rationalStar.Full ∧ (S.coefficient E).rationalStar.Faithful := by
    obtain ⟨I⟩ := SfStrictDirectImageScalar.strictDirectImageIntegralModel l E k hℓ i
    obtain ⟨hfull, hfaithful⟩ := closed_completed_fullyFaithful l E i U hU
    obtain ⟨hIfull, hIfaithful⟩ := restriction_fullyFaithful I.image _
      (sfIntegralConstructible l E Z).ι _ I.reconstruction.symm
    let eI := Functor.fullyFaithfulCancelRight (sfIntegralConstructible l E X).ι
      ((S.coefficient E).integralComparison ≪≫ I.reconstruction)
    let R := ScalarLocalization.transport (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionUniformizer l E) I.image
    have hR : R.Full ∧ R.Faithful := localized_fullyFaithful _ _ I.image
    have eQ : sfRationalConstructibleLocalization l E Z ⋙ R ≅
        I.image ⋙ sfRationalConstructibleLocalization l E X :=
      NatIso.ofComponents (fun K ↦ Iso.refl _) (by
        intro K L f
        simp [R, sfRationalConstructibleLocalization, ScalarLocalization.transport,
          ScalarLocalization.transportHom, ScalarLocalization.localization])
    obtain ⟨e, _, _⟩ := ScalarLocalization.naturalIso_of_integral
      (Padic.coefficientExtensionIntegers l E) (sfIntegralConstructibleCategory l E Z)
      (Padic.coefficientExtensionUniformizer l E) (S.coefficient E).rationalStar R
      ((S.coefficient E).rationalComparison ≪≫
        Functor.isoWhiskerRight eI (sfRationalConstructibleLocalization l E X) ≪≫ eQ.symm)
    have := hR.1
    have := hR.2
    exact ⟨Functor.Full.of_iso e.symm, Functor.Faithful.of_iso e.symm⟩
  let F : (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Z).Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X) := {
    Φ := fun E ↦ (S.coefficient
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)).rationalStar
    β := S.scalarComparison
    coh := S.scalarCoherence }
  have hΦ (E : AlgebraicallyClosedCoefficients.Index l Ω) : (F.Φ E).FullyFaithful := by
    obtain ⟨hfull, hfaithful⟩ := hr (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
    exact .ofFullyFaithful _
  have : F.functor.Full := sfPairFull F hΦ
  have : F.functor.Faithful := sfPairFaithful F hΦ
  let e := stage_presentation_iso F S.algebraicallyClosedStar
    S.inclusionComparison S.inclusionCoherence
  have : S.algebraicallyClosedStar.Full := Functor.Full.of_iso e.symm
  have : S.algebraicallyClosedStar.Faithful := Functor.Faithful.of_iso e.symm
  refine ⟨?_, ⟨inferInstance, inferInstance⟩, ?_⟩
  · intro E _ _ _
    have := (hi E).1
    have := (hi E).2
    have := (hr E).1
    have := (hr E).2
    refine ⟨hf E, ⟨inferInstance, inferInstance⟩, ⟨inferInstance, inferInstance⟩,
      ?_, ?_, ?_, ?_⟩
    · intro n hn G adj Q
      have := (hf E n hn).1
      have := (hf E n hn).2
      have := adj.unit_isIso_of_L_fully_faithful
      infer_instance
    · intro G adj Q
      have := adj.unit_isIso_of_L_fully_faithful
      infer_instance
    · intro G adj Q
      have := adj.unit_isIso_of_L_fully_faithful
      infer_instance
    · intro n hn
      let := Padic.finite_coefficientExtensionRing l E n hn
      obtain ⟨_, ⟨adj⟩⟩ := Scheme.sfIntrinsicClosedAmbientAdjunction
        (Padic.coefficientExtensionRing l E n) i O.ι
        (by change IsCompl (Set.range i) (Set.range U.hom); rw [hU]; exact isCompl_compl)
      have he : Scheme.sfConstantModuleDirectImage i
          (Padic.coefficientExtensionRing l E n) =
          Scheme.proEtaleConstantModuleDirectImage i
            (Padic.coefficientExtensionRing l E n) := constant_direct_image_eq _ _
      let adj' := adj.ofNatIsoLeft (Functor.rightDerivedFunctorNatIso (eqToIso he))
      obtain ⟨hfull, hfaithful⟩ := closed_constant_fullyFaithful i U hU
        (Padic.coefficientExtensionRing l E n)
      refine ⟨_, adj', ?_⟩
      intro Q
      have := adj'.unit_isIso_of_L_fully_faithful
      infer_instance
  · intro G adj Q
    have := adj.unit_isIso_of_L_fully_faithful
    infer_instance


/-- The actual closed direct images admit fully faithful restrictions at all four
stages. Existence of the comparison squares includes preservation of the relevant
constructible categories. At the algebraically closed stage the comparison is a
natural isomorphism on every finite coefficient stage, compatible with the
scalar comparisons and the canonical change-of-stage arrows.
The finite ambient right adjoint exists and its unit is invertible on every object,
without a boundedness or constructibility assumption. For each restricted functor,
the unit is invertible for every right adjoint whenever one exists.

Source: Weil blueprint, sec-smooth-purity/sk-prop-sf-closed-unit, order 1861
(blueprint: prop-sf-closed-unit-all-stages).

Proof (all assertions postponed at stage 2):
1. Finite type over a field makes X and Z Noetherian. Their complementary open
immersion is quasi-compact. A closed immersion is proper; its identity/open,
closed/proper compactification identifies Ri_! with Ri_* at every stage.
2. The open--closed recollement counit i^* Ri_* to id is invertible. Thus finite
ambient Ri_* is fully faithful. Closed direct image is exact. Extend a finite
constructible stratification of Z by the zero sheaf on its open complement; this
proves preservation and supplies finiteStar and finiteComparison.
3. Identify the completed-coefficient image with the strict finite-image tower
using the projection-normalized comparison. Integral constructibility and the
actual reduction comparisons give its integral restriction and integralComparison.
Apply Hom to the source and image Roos triangles. Scalar-extension/restriction
adjunction identifies the maps into finite terms with finite direct image on Hom.
The product maps are bijective. Exact five-term rows then give the integral Hom
bijection, transported through the natural completed/tower comparison.
4. Tensor the integral Hom map and its inverse with E. This gives the additive,
localized-linear rational restriction and rationalComparison; no Karoubi envelope
is introduced.
5. Use the canonical finite scalar-extension comparisons for direct image. Their
coherence lets the rational restrictions descend to the existing common-stage
category and gives the displayed inclusion comparisons, scalarCoherence and
inclusionCoherence. These equations identify the image of a representative with
the finite-stage direct image conjugated by the specified scalar comparisons.
At each common finite
field the Hom map is bijective. Apply its inverse to a representative; coherence
and injectivity make this independent of the chosen common field. Thus the
algebraically closed image is fully faithful.
6. For each right adjoint, postcomposition with its unit corresponds under the
adjunction to the fully faithful direct image on Hom. Yoneda makes the unit an
isomorphism, with no Full or Faithful premise. Finite ambient closed support gives
the right adjoint and the same unit assertion for all ambient objects, as in
prop-sf-closed-immersion-unit. -/
theorem closedUnitAllStages
    (k : Type u) [Field k]
    (l : ℕ) [Fact l.Prime] (hℓ : IsUnit (l : k))
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {Z X : Scheme.{u}} [Z.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))] [LocallyOfFiniteType (Z ↘ Spec (.of k))]
    [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (i : Z ⟶ X) [i.IsOver (Spec (.of k))] [IsClosedImmersion i] :
    Nonempty (ClosedDirectImageStages l Ω i) ∧
    ∀ S : ClosedDirectImageStages l Ω i,
      (∀ (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E],
        (∀ (n : ℕ) (hn : 1 ≤ n),
          ((S.coefficient E).finiteStar n hn).Full ∧
            ((S.coefficient E).finiteStar n hn).Faithful) ∧
        ((S.coefficient E).integralStar.Full ∧
          (S.coefficient E).integralStar.Faithful) ∧
        ((S.coefficient E).rationalStar.Full ∧
          (S.coefficient E).rationalStar.Faithful) ∧
        (∀ (n : ℕ) (hn : 1 ≤ n)
          (G : (Scheme.intrinsicFiniteTorsionConstructible l E n hn X).FullSubcategory ⥤
            (Scheme.intrinsicFiniteTorsionConstructible l E n hn Z).FullSubcategory)
          (adj : (S.coefficient E).finiteStar n hn ⊣ G), ∀ Q, IsIso (adj.unit.app Q)) ∧
        (∀ (G : sfIntegralConstructibleCategory l E X ⥤
            sfIntegralConstructibleCategory l E Z)
          (adj : (S.coefficient E).integralStar ⊣ G), ∀ Q, IsIso (adj.unit.app Q)) ∧
        (∀ (G : sfRationalConstructibleCategory l E X ⥤
            sfRationalConstructibleCategory l E Z)
          (adj : (S.coefficient E).rationalStar ⊣ G), ∀ Q, IsIso (adj.unit.app Q)) ∧
        (∀ (n : ℕ) (_hn : 1 ≤ n),
          ∃ G : Scheme.proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n) ⥤
              Scheme.proEtaleDerivedCategory Z (Padic.coefficientExtensionRing l E n),
          ∃ adj : Scheme.proEtaleConstantDerivedDirectImage i
              (Padic.coefficientExtensionRing l E n) ⊣ G,
            ∀ Q, IsIso (adj.unit.app Q))) ∧
      (S.algebraicallyClosedStar.Full ∧ S.algebraicallyClosedStar.Faithful) ∧
      (∀ (G : generalAlgebraicallyClosedConstructibleCategory l Ω X ⥤
          generalAlgebraicallyClosedConstructibleCategory l Ω Z)
        (adj : S.algebraicallyClosedStar ⊣ G), ∀ Q, IsIso (adj.unit.app Q)) := by
  refine ⟨closedUnitAllStages_exists k l hℓ Ω i, ?_⟩
  intro S
  exact closedUnitAllStages_properties k l hℓ Ω i S

end WeilConjectures
