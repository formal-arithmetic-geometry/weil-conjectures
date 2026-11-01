/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothLisseIntegralLattice
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.LatticeSheafBasicSupplement
import WeilConjectures.CategoryTheory.RingedLocalizationIso
import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientCompletionSupplement
import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientLocalization
import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousConstructibleModule
import all WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompletedCoefficientPresentationAt

/-! # The normalized continuous and completed coefficient square

Source: Bhatt--Scholze, Lemmas 6.8.2(1),(2) and Definition 6.8.3.
(blueprint: lem-zl-continuous-completed-localization-square)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.ProEtale
open Scheme
open WeilConjectures
open WeilConjectures.LocallyFiniteAdicCompactSupport

private def liftFunctionsIso (X : Scheme.{u}) (R : Type u)
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    latticeCoefficientSheaf X R ≅ continuousCoefficientSheaf X (ULift.{u + 1} R) where
  hom := ⟨{
    app := fun U ↦ CommRingCat.ofHom {
      toFun := fun s ↦ ⟨fun x ↦ ULift.up (s.down x),
        continuous_uliftUp.comp s.down.continuous⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
    naturality := fun _ _ _ ↦ rfl }⟩
  inv := ⟨{
    app := fun U ↦ CommRingCat.ofHom {
      toFun := fun s ↦ ULift.up ⟨fun x ↦ (s x).down,
        continuous_uliftDown.comp s.continuous⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
    naturality := fun _ _ _ ↦ rfl }⟩
  hom_inv_id := by ext U s; rfl
  inv_hom_id := by ext U s; rfl

private def continuousConstantSection (X : Scheme.{u})
    (T : Type (u + 1)) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T] (t : T) :
    ((continuousCoefficientSheaf X T).obj ⋙ forget CommRingCat).sections :=
  ⟨fun U ↦ ContinuousMap.const U.unop.left t, fun _ ↦ rfl⟩

private def continuousLocalizationPresentation (X : Scheme.{u})
    (T : Type (u + 1)) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T] (t : T) :
    ringedLocalizationRingPresheafOfUniverses.{u + 1, u + 1, u}
        (J := ProEt.topology X) (continuousCoefficientSheaf X T)
        (continuousConstantSection X T t) ≅ localizedContinuousMapPresheaf X T t :=
  NatIso.ofComponents (fun U ↦ Iso.refl (CommRingCat.of
    (Localization.Away (ContinuousMap.const U.unop.left t)))) (by
    intro U V f
    apply CommRingCat.hom_ext
    change ringedSectionLocalizationMapOfUniverses (continuousCoefficientSheaf X T)
        (continuousConstantSection X T t) f = localizedContinuousMapRestriction X T t f
    apply IsLocalization.ringHom_ext
      (R := C(U.unop.left, T))
      (S := Localization.Away (ContinuousMap.const U.unop.left t))
      (Submonoid.powers (ContinuousMap.const U.unop.left t))
    ext z
    simp only [ringedSectionLocalizationMapOfUniverses, RingHom.comp_apply,
      localizedContinuousMapRestriction, IsLocalization.Away.map]
    rfl)

private theorem completedScalarSquare
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (c : integralCoefficientSheaf l X E ≅ finiteCoefficientLimit l X E)
    (hc : ∀ n : ℕ, ∃ q : (constantSheaf (ProEt.topology X)
        CommRingCat.{u + 1}).obj (finiteCoefficientRing l E n) ≅
        finiteContinuousCoefficientSheaf l X E n,
      (∀ (U : X.ProEtᵒᵖ) (a : finiteCoefficientRing l E n) (x : U.unop.left),
        finiteContinuousCoefficientValue l E X n U
          (q.hom.hom.app U ((toSheafify (ProEt.topology X)
            ((Functor.const X.ProEtᵒᵖ).obj (finiteCoefficientRing l E n))).app U a)) x = a) ∧
      (∀ (U : X.ProEtᵒᵖ) (s : (integralCoefficientSheaf l X E).obj.obj U)
        (x : U.unop.left),
        (finiteContinuousCoefficientValue l E X n U
          ((c.hom ≫ limit.π (finiteCoefficientTower l X E) (op n) ≫ q.hom).hom.app U s)
            x).down = Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
              (integralCoefficientValue l E X U s x))) :
    let := coefficientExtensionNormedField l E
    let H := sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
    H.map (continuousCoefficientConstantMap X (Padic.coefficientExtensionIntegers l E) ≫
      (liftFunctionsIso X (Padic.coefficientExtensionIntegers l E)).hom ≫ c.hom ≫
        (completionIso l E X).hom) = integralConstantToCompletionOfUniverses l E X := by
  let := coefficientExtensionNormedField l E
  let H := sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  apply limit.hom_ext
  intro n
  simp only [Functor.map_comp, Category.assoc]
  have hp : H.map (completedIntegralCommRingProjectionUnrestricted l E X n.unop) =
      limit.π (integralCoefficientSheafSystem l E X) n := by
    cases n
    rfl
  rw [← hp, ← H.map_comp, completionIso_projection]
  rw [hp, integralConstantToCompletionOfUniverses, limit.lift_π]
  erw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  change H.map _ = H.map _
  apply congrArg H.map
  obtain ⟨q, hq, hcq⟩ := hc n.unop
  apply (cancel_mono q.hom).mp
  apply ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
    ((Functor.const X.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))) _).injective
  simp only [constantSheaf, Functor.comp_map, Category.assoc]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [continuousCoefficientConstantMap, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  let : TopologicalSpace (finiteCoefficientRing l E n.unop) := ⊥
  let : DiscreteTopology (finiteCoefficientRing l E n.unop) := ⟨rfl⟩
  apply ContinuousMap.ext
  intro x
  apply ULift.ext
  exact (hcq U ((liftFunctionsIso X (Padic.coefficientExtensionIntegers l E)).hom.hom.app U
    ((continuousCoefficientConstants X (Padic.coefficientExtensionIntegers l E)).app U a)) x)
    |>.trans (congrArg ULift.down (hq U (ULift.up
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n.unop + 1)) a.down)) x)).symm

/-- Continuous integral and rational coefficients identify with the completed integral
ring and its uniformizer localization, preserving the actual inclusion.
Source: Bhatt--Scholze, Lemmas 6.8.2(1),(2) and Definition 6.8.3.
(blueprint: lem-zl-continuous-completed-localization-square)

Proof. Exchange the two universe-lift conventions on continuous functions. The
continuous completion comparison identifies integral functions with compatible finite
residues, and the limit comparison identifies that tower with the recorded completion.
Checking every finite projection fixes constant scalars, hence the uniformizer section.
Localize this integral isomorphism and compose with the continuous localization
isomorphism. Its numerator normalization gives the square of the two actual inclusions.
The comparisons are pointwise and therefore include empty objects and the zero ring. -/
private theorem continuousCompletedLocalizationSquareAux
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :
    let := coefficientExtensionNormedField l E
    ∃ c : latticeCoefficientSheaf X (Padic.coefficientExtensionIntegers l E) ≅
        completedIntegralCommRingSheafUnrestricted l E X,
      ∃ q : latticeCoefficientSheaf X E ≅ smoothLatticeRationalRing l E X,
        latticeCoefficientSheafMap X (Padic.coefficientExtensionIntegers l E).subtype
          continuous_subtype_val ≫ q.hom = c.hom ≫ smoothLatticeCoefficientMap l E X := by
  let := coefficientExtensionNormedField l E
  let A := Padic.coefficientExtensionIntegers l E
  let R := integralCoefficientSheaf l X E
  let B := completedIntegralCommRingSheafUnrestricted l E X
  let p := Padic.coefficientExtensionUniformizer l E
  obtain ⟨a, ha⟩ := continuousCoefficientCompletion l E X
  let c₀ : R ≅ B := a ≪≫ completionIso l E X
  let s : (R.obj ⋙ forget CommRingCat).sections :=
    ⟨fun U ↦ ContinuousMap.const U.unop.left (ULift.up p), fun _ ↦ rfl⟩
  let t := smoothLatticeUniformizerSection l E X
  have hst (U : X.ProEtᵒᵖ) : c₀.hom.hom.app U (s.val U) = t.val U := by
    have h := completedScalarSquare l E X a ha
    have hto : toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A))) ≫
          (continuousCoefficientConstantMap X A).hom =
        continuousCoefficientConstants X A :=
      (sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
        _ _ |>.apply_symm_apply _
    have h' := congrArg (fun f ↦ f.hom.app U
      ((toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app U
          (ULift.up p))) h
    change c₀.hom.hom.app U
      ((liftFunctionsIso X A).hom.hom.app U
        ((continuousCoefficientConstantMap X A).hom.app U _)) = _ at h'
    have hto' := ConcreteCategory.congr_hom (NatTrans.congr_app hto U) (ULift.up p)
    change (continuousCoefficientConstantMap X A).hom.app U _ =
      ULift.up (ContinuousMap.const U.unop.left p) at hto'
    erw [hto'] at h'
    exact h'
  obtain ⟨d, hd⟩ := ringedLocalization_iso c₀ s t hst
  let ep := continuousLocalizationPresentation X (ULift.{u + 1} A) (ULift.up p)
  let d₀ : ringedLocalizationRingOfUniverses.{u + 1, u + 1, u}
      (J := ProEt.topology X) R s ≅ integralCoefficientLocalization l X E :=
    (presheafToSheaf (ProEt.topology X) CommRingCat.{u + 1}).mapIso ep
  obtain ⟨b, hb⟩ := continuousCoefficientLocalization l E X
  have hnum : ringedLocalizationRingUnitOfUniverses.{u + 1, u + 1, u}
        (J := ProEt.topology X) R s ≫ d₀.hom ≫ b.hom =
      integralRationalCoefficientMap l E X := by
    apply Sheaf.hom_ext
    change (ringedLocalizationRingPresheafUnitOfUniverses.{u + 1, u + 1, u}
      (J := ProEt.topology X) R s ≫
      toSheafify (ProEt.topology X) _) ≫
        ((presheafToSheaf (ProEt.topology X) CommRingCat.{u + 1}).map ep.hom).hom ≫
          b.hom.hom = (integralRationalCoefficientMap l E X).hom
    erw [Category.assoc, ← toSheafify_naturality_assoc]
    ext U z
    apply ContinuousMap.ext
    intro x
    apply ULift.ext
    exact hb U z x
  let c : latticeCoefficientSheaf X A ≅ B := liftFunctionsIso X A ≪≫ c₀
  let q : latticeCoefficientSheaf X E ≅ smoothLatticeRationalRing l E X :=
    liftFunctionsIso X E ≪≫ b.symm ≪≫ d₀.symm ≪≫ d
  refine ⟨c, q, ?_⟩
  have hi : latticeCoefficientSheafMap X A.subtype continuous_subtype_val ≫
      (liftFunctionsIso X E).hom =
      (liftFunctionsIso X A).hom ≫ integralRationalCoefficientMap l E X := by
    ext U z
    rfl
  dsimp only [q, c, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc, hi]
  rw [← hnum]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  erw [Category.assoc, hd]
  rfl

/-- The completed and continuous localization square for the canonical spectral topology.
Source: Bhatt--Scholze, Lemmas 6.8.2(1),(2) and Definition 6.8.3.
(blueprint: lem-zl-continuous-completed-localization-square)

Proof. The extending absolute value and spectral norm have equal distances, hence
identical topologies. Apply the normalized coefficient square in that topology. -/
theorem continuousCompletedLocalizationSquare
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :
    let := spectralNorm.normedField ℚ_[l] E
    ∃ c : latticeCoefficientSheaf X (Padic.coefficientExtensionIntegers l E) ≅
        completedIntegralCommRingSheafUnrestricted l E X,
      ∃ q : latticeCoefficientSheaf X E ≅ smoothLatticeRationalRing l E X,
        latticeCoefficientSheafMap X (Padic.coefficientExtensionIntegers l E).subtype
          continuous_subtype_val ≫ q.hom = c.hom ≫ smoothLatticeCoefficientMap l E X := by
  have hm : (coefficientExtensionNormedField l E).toPseudoMetricSpace =
      (spectralNorm.normedField ℚ_[l] E).toPseudoMetricSpace :=
    PseudoMetricSpace.ext (by
      apply Dist.ext
      funext x y
      change spectralNorm ℚ_[l] E (-x + y) = spectralNorm ℚ_[l] E (x - y)
      rw [show -x + y = -(x - y) by abel,
        spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic _)])
  have ht :
      (letI := coefficientExtensionNormedField l E; inferInstance : TopologicalSpace E) =
      (letI := spectralNorm.normedField ℚ_[l] E; inferInstance : TopologicalSpace E) :=
    congrArg (fun m : PseudoMetricSpace E ↦ m.toUniformSpace.toTopologicalSpace) hm
  let P (t : TopologicalSpace E) : Prop :=
    letI := t
    ∀ _ : IsTopologicalRing E,
      ∃ c : latticeCoefficientSheaf X (Padic.coefficientExtensionIntegers l E) ≅
          completedIntegralCommRingSheafUnrestricted l E X,
        ∃ q : latticeCoefficientSheaf X E ≅ smoothLatticeRationalRing l E X,
          latticeCoefficientSheafMap X (Padic.coefficientExtensionIntegers l E).subtype
            continuous_subtype_val ≫ q.hom = c.hom ≫ smoothLatticeCoefficientMap l E X
  have h : P (letI := coefficientExtensionNormedField l E; inferInstance) := by
    intro htop
    exact continuousCompletedLocalizationSquareAux l E X
  have h' : P (letI := spectralNorm.normedField ℚ_[l] E; inferInstance) :=
    ht ▸ h
  let := spectralNorm.normedField ℚ_[l] E
  exact h' inferInstance

end AlgebraicGeometry.ProEtale
