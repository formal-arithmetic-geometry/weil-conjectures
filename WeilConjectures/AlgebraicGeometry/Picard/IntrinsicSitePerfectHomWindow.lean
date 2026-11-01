/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Supporting.LegacySitePerfectComplex
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
import WeilConjectures.CategoryTheory.Ringed.Site.RingedSitePerfectDuality
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # The coefficient dual and Tor interval of a site-perfect complex

This specializes the ringed-site perfect-duality argument to the specified
finite intrinsic tensor and internal Hom, without geometric constructibility assumptions.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u uC vC wC
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules
namespace WeilConjectures

attribute [local irreducible] finiteIntrinsicClosed derivedInternalHomOfUniverses

/-- The uncurried tensor and the left tensor functor have the same maps. -/
private def tensorLeftSectionIso {D : Type*} [Category D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (P : D) :
    @tensorLeft D _ S.monoidal P ≅ Prod.sectR P D ⋙ S.tensor := by
  let := S.monoidal
  refine NatIso.ofComponents (fun _ ↦ Iso.refl _) ?_
  intro X Y f
  simp [CoefficientClosedStructure.tensor, MonoidalCategory.tensor, Prod.sectR]

private theorem tor_tests_iff
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory.{wC} C] [MonoidalCategory C] [MonoidalClosed C]
    [MonoidalPreadditive C] [BraidedCategory C]
    [DerivedCategory.Qh.HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso C (.up ℤ))]
    (B : CochainComplex C ℤ → Prop)
    (T : ∀ G _N P : CochainComplex C ℤ, (f : P ⟶ G) → QuasiIso f → B P →
      DerivedCategory C)
    (heq : ∀ (G N P : CochainComplex C ℤ) (f : P ⟶ G) (hf : QuasiIso f) (hP : B P),
      Nonempty (tensorObj (DerivedCategory.Q.obj G) (DerivedCategory.Q.obj N) ≅
        T G N P f hf hP))
    (hres : ∀ G : CochainComplex C ℤ,
      ∃ (P : CochainComplex C ℤ) (f : P ⟶ G), B P ∧ QuasiIso f)
    (Z : DerivedCategory C) (a b : ℤ) (hab : a ≤ b) :
    (a ≤ b ∧ ∀ G P : CochainComplex C ℤ, Nonempty (DerivedCategory.Q.obj G ≅ Z) →
      ∀ (f : P ⟶ G) (hf : QuasiIso f) (hP : B P) (N : C) (i : ℤ),
      (i < a ∨ b < i) → IsZero ((DerivedCategory.homologyFunctor C i).obj
        (T G ((HomologicalComplex.single C (.up ℤ) 0).obj N) P f hf hP))) ↔
      DerivedCategory.torAmplitudeIn C a b Z := by
  classical
  constructor
  · intro h M
    let G := (DerivedCategory.Q (C := C)).objPreimage Z
    let e := (DerivedCategory.Q (C := C)).objObjPreimageIso Z
    obtain ⟨P, f, hP, hf⟩ := hres G
    obtain ⟨eq⟩ := heq G ((HomologicalComplex.single C (.up ℤ) 0).obj M) P f hf hP
    let eq' := tensorIso (show Z ≅ DerivedCategory.Q.obj G from e.symm)
      ((DerivedCategory.singleFunctorIsoCompQ C 0).app M) ≪≫ eq
    refine ⟨(DerivedCategory.isGE_iff _ a).2 ?_, (DerivedCategory.isLE_iff _ b).2 ?_⟩
    · intro i hi
      exact (h.2 G P ⟨e⟩ f hf hP M i (.inl hi)).of_iso
        ((DerivedCategory.homologyFunctor C i).mapIso eq')
    · intro i hi
      exact (h.2 G P ⟨e⟩ f hf hP M i (.inr hi)).of_iso
        ((DerivedCategory.homologyFunctor C i).mapIso eq')
  · intro h
    refine ⟨hab, ?_⟩
    rintro M P ⟨e⟩ f hf hP N i hi
    obtain ⟨eq⟩ := heq M ((HomologicalComplex.single C (.up ℤ) 0).obj N) P f hf hP
    let eq' := tensorIso (show Z ≅ DerivedCategory.Q.obj M from e.symm)
      ((DerivedCategory.singleFunctorIsoCompQ C 0).app N) ≪≫ eq
    have hz : IsZero ((DerivedCategory.homologyFunctor C i).obj
        (tensorObj Z ((DerivedCategory.singleFunctor C 0).obj N))) := by
      obtain ⟨hge, hle⟩ := h N
      rcases hi with hi | hi
      · exact (DerivedCategory.isGE_iff _ a).1 hge i hi
      · exact (DerivedCategory.isLE_iff _ b).1 hle i hi
    exact hz.of_iso ((DerivedCategory.homologyFunctor C i).mapIso eq'.symm)

private theorem intrinsic_tensor_eq
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (n : ℕ) :
    finiteIntrinsicDerivedTensor l E X n = (finiteIntrinsicClosed l E X n).tensor := rfl

attribute [local irreducible] finiteIntrinsicDerivedTensor

private theorem intrinsic_tensor_tor
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (n : ℕ)
    (K L : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1)))
    (a b c d : ℤ)
    (hK : HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1)) K a b)
    (hL : HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1)) L c d) :
    HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
      ((finiteIntrinsicDerivedTensor l E X n).obj (K, L)) (a + c) (b + d) := by
  classical
  let := integralCoefficientAbSheafify.{u, u} X
  let := integralCoefficientAbLocallyBijective.{u, u} X
  let : EssentiallySmall.{u+1} X.ProEt := essentiallySmallSelf.{0, u, u+1} _
  let A : Type u := Padic.coefficientExtensionRing l E (n + 1)
  let R : Sheaf (ProEt.topology X) CommRingCat.{u+1} :=
    integralCoefficientCommRingSheaf l E X n
  let C := SheafOfModules.{u+1}
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u+1} RingCat.{u+1})).obj R)
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{u+1, u, u+1} R
  let := SheafOfModules.cochainModulesMonoidal.{u+1, u, u+1} R
  let := SheafOfModules.cochainModulesSymmetric.{u+1, u, u+1} R
  let := SheafOfModules.cochainModulesPreadditive.{u+1, u, u+1} R
  let := (nonempty_monoidalClosed_independentCoefficients.{u+1, u+1, u} (R := R)).some
  have hGroth :=
    grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u+1, u, u+1}
      (ProEt.topology X) R
  let := hGroth.1
  let := SheafOfModules.hasFunctorialFlatResolution_kfi.{u+1, u+1, u} R
  let : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} C
  let := HasDerivedCategory.standard C
  let := DerivedCategory.hasDerivedMonoidalCategory C
  let : MonoidalCategory (DerivedCategory C) :=
    DerivedCategory.instMonoidalCategory_weilConjectures.{u+2, u+1, u+2} C
  change DerivedCategory C at K L
  have heq (M N P : CochainComplex C ℤ) (f : P ⟶ M) (hf : QuasiIso f)
      (hP : CochainComplex.IsAcyclicTensorKFlat (R := R) P) :
      Nonempty (tensorObj (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj N) ≅
        derivedTensor X A M N P f hf hP) := by
    have : IsIso (DerivedCategory.Q.map f) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso C f).2 hf
    exact ⟨tensorIso (asIso (DerivedCategory.Q.map f)).symm (Iso.refl _) ≪≫
      (RingedDerivedNative.tensorIso.{u+1, u, u, u+2} (ProEt.topology X) R P N
        (Or.inl ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hP))).symm⟩
  have hamp (Z : DerivedCategory C) (a b : ℤ) (hab : a ≤ b) :
      HasProEtaleTorAmplitude X A Z a b ↔ DerivedCategory.torAmplitudeIn C a b Z := by
    apply tor_tests_iff (C := C) (B := CochainComplex.IsAcyclicTensorKFlat (R := R))
      (T := derivedTensor X A) heq ?_ Z a b hab
    intro G
    obtain ⟨P, f, hP, _, hf, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients G
    exact ⟨P, f, (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).1 hP, hf⟩
  have hK' := (hamp _ a b hK.1).1 hK
  have hL' := (hamp _ c d hL.1).1 hL
  have hT := DerivedCategory.torAmplitudeIn_tensor hK' hL'
  obtain ⟨S, hS, _, _⟩ := RingedDerivedNative.closedAdjunction.{u+1, u, u, u+2}
    (ProEt.topology X) R
  let e : (finiteIntrinsicClosed l E X n).tensor.obj (K, L) ≅
      S.tensor.obj (K, L) :=
    (Adjunction.leftAdjointUniq
    ((finiteIntrinsicClosed l E X n).adjunction L) (S.adjunction L)).app K
  have e' : Nonempty ((finiteIntrinsicDerivedTensor l E X n).obj (K, L) ≅
      @tensorObj (DerivedCategory C) _
        (RingedDerivedNative.monoidal.{u+1, u, u, u+2}
          (ProEt.topology X) R).toMonoidalCategoryStruct K L) := by
    rw [intrinsic_tensor_eq]
    refine ⟨e ≪≫ eqToIso ?_⟩
    exact congrArg (fun m : MonoidalCategory (DerivedCategory C) ↦
      @tensorObj (DerivedCategory C) _ m.toMonoidalCategoryStruct K L) hS
  obtain ⟨e'⟩ := e'
  have ht := (hamp (tensorObj K L) (a + c) (b + d)
    (add_le_add hK.1 hL.1)).2 hT
  refine ⟨add_le_add hK.1 hL.1, ?_⟩
  intro G P hG f hf hP N i hi
  exact ht.2 G P (hG.map (fun j ↦ j ≪≫ e')) f hf hP N i hi


private theorem intrinsic_dual_tor
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (n : ℕ)
    (K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1)))
    (hperfect : IsFiniteCoefficientSitePerfect l E X n K)
    (a b : ℤ)
    (hK : HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1)) K a b) :
    HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
      ((finiteIntrinsicDerivedInternalHom l E X n).obj
        (op K, ringedSiteDualityUnit.{u+1, u, u, u+2}
          (ProEt.topology X) (integralCoefficientCommRingSheaf l E X n))) (-b) (-a) := by
  classical
  let := integralCoefficientAbSheafify.{u, u} X
  let := integralCoefficientAbLocallyBijective.{u, u} X
  let : EssentiallySmall.{u+1} X.ProEt := essentiallySmallSelf.{0, u, u+1} _
  let A : Type u := Padic.coefficientExtensionRing l E (n + 1)
  let R : Sheaf (ProEt.topology X) CommRingCat.{u+1} :=
    integralCoefficientCommRingSheaf l E X n
  let C := SheafOfModules.{u+1}
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u+1} RingCat.{u+1})).obj R)
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{u+1, u, u+1} R
  let := SheafOfModules.cochainModulesMonoidal.{u+1, u, u+1} R
  let := SheafOfModules.cochainModulesSymmetric.{u+1, u, u+1} R
  let := SheafOfModules.cochainModulesPreadditive.{u+1, u, u+1} R
  let := (nonempty_monoidalClosed_independentCoefficients.{u+1, u+1, u} (R := R)).some
  have hGroth :=
    grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u+1, u, u+1}
      (ProEt.topology X) R
  let := hGroth.1
  let := SheafOfModules.hasFunctorialFlatResolution_kfi.{u+1, u+1, u} R
  let : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} C
  let := HasDerivedCategory.standard C
  let := DerivedCategory.hasDerivedMonoidalCategory C
  let : MonoidalCategory (DerivedCategory C) :=
    DerivedCategory.instMonoidalCategory_weilConjectures.{u+2, u+1, u+2} C
  let : SymmetricCategory (DerivedCategory C) :=
    RingedDerivedNative.symmetric.{u+1, u, u, u+2} (ProEt.topology X) R
  change DerivedCategory C at K
  have heq (M N P : CochainComplex C ℤ) (f : P ⟶ M) (hf : QuasiIso f)
      (hP : CochainComplex.IsAcyclicTensorKFlat (R := R) P) :
      Nonempty (tensorObj (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj N) ≅
        derivedTensor X A M N P f hf hP) := by
    have : IsIso (DerivedCategory.Q.map f) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso C f).2 hf
    exact ⟨tensorIso (asIso (DerivedCategory.Q.map f)).symm (Iso.refl _) ≪≫
      (RingedDerivedNative.tensorIso.{u+1, u, u, u+2} (ProEt.topology X) R P N
        (Or.inl ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hP))).symm⟩
  have hamp (Z : DerivedCategory C) (a b : ℤ) (hab : a ≤ b) :
      HasProEtaleTorAmplitude X A Z a b ↔ DerivedCategory.torAmplitudeIn C a b Z := by
    apply tor_tests_iff (C := C) (B := CochainComplex.IsAcyclicTensorKFlat (R := R))
      (T := derivedTensor X A) heq ?_ Z a b hab
    intro G
    obtain ⟨P, f, hP, _, hf, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients G
    exact ⟨P, f, (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).1 hP, hf⟩
  let := integralCoefficientAbSheafify.{u, u} X
  let := integralCoefficientAbLocallyBijective.{u, u} X
  let : ∀ U : X.ProEt, HasSheafify ((ProEt.topology X).over U)
      AddCommGrpCat.{u+1} := fun U ↦ sitePerfectOverAbSheafify.{u, u} X U
  let : ∀ U : X.ProEt, ((ProEt.topology X).over U).WEqualsLocallyBijective
      AddCommGrpCat.{u+1} := fun U ↦ sitePerfectOverAbLocallyBijective.{u, u} X U
  let O : DerivedCategory C := ringedSiteDualityUnit.{u+1, u, u, u+2} (ProEt.topology X) R
  let H : (DerivedCategory C)ᵒᵖ × DerivedCategory C ⥤ DerivedCategory C :=
    finiteIntrinsicDerivedInternalHom l E X n
  let D := H.obj (op K, O)
  obtain ⟨M, hD, hbidual, hM⟩ := ringedSitePerfectDuality.{u+1, u, u, u+2}
    (ProEt.topology X) R K hperfect
  obtain ⟨MD, _, _, hMD⟩ := ringedSitePerfectDuality.{u+1, u, u, u+2}
    (ProEt.topology X) R D hD
  obtain ⟨S, hS, _, _⟩ := RingedDerivedNative.closedAdjunction.{u+1, u, u, u+2}
    (ProEt.topology X) R
  let rightComp (M : RingedSiteDualityModel.{u+1, u, u, u+2} (ProEt.topology X) R)
      (P : DerivedCategory C) :
      tensorRight P ≅ @tensorRight _ _ M.closed.monoidal P :=
    eqToIso (congrArg (fun m : MonoidalCategory (DerivedCategory C) ↦
      @tensorRight _ _ m P) hS.symm) ≪≫
        Adjunction.leftAdjointUniq (S.adjunction P) (M.closed.adjunction P)
  let leftComp (M : RingedSiteDualityModel.{u+1, u, u, u+2} (ProEt.topology X) R)
      (P : DerivedCategory C) :
      tensorLeft P ≅ @tensorLeft _ _ M.closed.monoidal P :=
    BraidedCategory.tensorLeftIsoTensorRight P ≪≫ rightComp M P ≪≫
      (@BraidedCategory.tensorLeftIsoTensorRight _ _ M.closed.monoidal
        M.symmetric.toBraidedCategory P).symm
  let qK : tensorLeft D ≅ Prod.sectR (op K) (DerivedCategory C) ⋙ H :=
    leftComp M D ≪≫ tensorLeftSectionIso M.closed D ≪≫
      @asIso _ _ _ _ _ hM
  let qD : tensorLeft (H.obj (op D, O)) ≅ Prod.sectR (op D) (DerivedCategory C) ⋙ H :=
    leftComp MD _ ≪≫ tensorLeftSectionIso MD.closed _ ≪≫
      @asIso _ _ _ _ _ hMD
  let eK : K ≅ H.obj (op D, O) :=
    @asIso _ _ _ _ _ hbidual
  -- Perfect evaluation and biduality identify the two right adjoints.
  let adjK : tensorLeft K ⊣ tensorLeft D :=
    ((S.adjunction K).ofNatIsoLeft (eqToIso (congrArg
      (fun m : MonoidalCategory (DerivedCategory C) ↦ @tensorRight _ _ m K) hS))).ofNatIsoRight
        qK.symm |>.ofNatIsoLeft (BraidedCategory.tensorLeftIsoTensorRight K).symm
  let adjD : tensorLeft D ⊣ tensorLeft K :=
    ((S.adjunction D).ofNatIsoLeft (eqToIso (congrArg
      (fun m : MonoidalCategory (DerivedCategory C) ↦ @tensorRight _ _ m D) hS))).ofNatIsoRight
        (qD.symm ≪≫ (curriedTensor (DerivedCategory C)).mapIso eK.symm)
          |>.ofNatIsoLeft (BraidedCategory.tensorLeftIsoTensorRight D).symm
  have hK' := (hamp _ a b hK.1).1 hK
  -- Orthogonality tests reverse the endpoints of the Tor interval.
  have htor : DerivedCategory.torAmplitudeIn C (-b) (-a) D := by
    intro F
    refine ⟨(DerivedCategory.TStructure.t.isGE_iff_orthogonal
        (-b - 1) (-b) (by omega) _).2 (fun Y f hY ↦ ?_),
      (DerivedCategory.TStructure.t.isLE_iff_orthogonal
        (-a) (-a + 1) rfl _).2 (fun Y f hY ↦ ?_)⟩
    · have : Y.IsLE (-b - 1) := hY
      have : DerivedCategory.TStructure.t.IsLE ((tensorLeft K).obj Y)
          (b + (-b - 1)) := DerivedCategory.isLE_tensor_of_torAmplitudeIn hK' Y (-b - 1)
      obtain ⟨g, rfl⟩ := (adjK.homEquiv Y ((DerivedCategory.singleFunctor C 0).obj F)).surjective f
      have hz : g = 0 := DerivedCategory.TStructure.t.zero g (b + (-b - 1)) 0 (by omega)
      have : (tensorLeft D).IsRightAdjoint := adjK.isRightAdjoint
      rw [hz, Adjunction.homEquiv_unit]
      simp only [Functor.map_zero, comp_zero]
    · have : Y.IsGE (-a + 1) := hY
      have : DerivedCategory.TStructure.t.IsGE ((tensorLeft K).obj Y)
          (a + (-a + 1)) := DerivedCategory.isGE_tensor_of_torAmplitudeIn hK' Y (-a + 1)
      have hz : adjD.homEquiv ((DerivedCategory.singleFunctor C 0).obj F) Y f = 0 :=
        DerivedCategory.TStructure.t.zero _ 0 (a + (-a + 1)) (by omega)
      have : (tensorLeft K).IsRightAdjoint := adjD.isRightAdjoint
      apply (adjD.homEquiv _ _).injective
      rw [hz, Adjunction.homEquiv_unit]
      simp only [Functor.map_zero, comp_zero]
  exact (hamp _ (-b) (-a) (neg_le_neg hK.1)).2 htor

/-- Site-perfect internal Hom is coefficient dual tensor, with the reversed Tor window.
Source: current blueprint, thm-sf-ctf-stability.proof.md, first paragraph;
lem-sfb-ringed-site-perfect-duality and lem-sf-site-perfect-tor-window
(blueprint: lem-sf-intrinsic-site-perfect-hom-window).

Proof: use the normalized K-flat comparisons of finiteIntrinsicTensorModels to
identify the chosen tensor with total tensor on representatives. The ringed-site
perfect-duality evaluation theorem identifies dual tensor with derived internal Hom;
uniqueness of the closed adjunction transports its evaluation to the chosen closed
structure, including the tensor unit. For an ordered input interval [a,b], the
site-perfect Tor-window theorem gives bounded finite-projective models supported
in [a,b] on a covering of each site object. Their ordinary duals represent derived
duals because Hom from a finite-projective term is exact. The dual terms are
finite-projective and supported in [-b,-a]. Choose a flat model of the second input
in [c,d]; alternatively test the same Hom complex against each degree-zero module.
The total dual tensor is supported in [c-b,d-a] and is K-flat. Restriction to the
covering slices is exact and monoidal, and sheaf cohomology vanishing is local,
so this is the global Tor interval. This includes empty slices and zero complexes;
no nonzero object or geometric dimension bound is used. -/
theorem finiteIntrinsic_sitePerfect_hom_window
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (n : ℕ)
    (K L : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1)))
    (hK : IsFiniteCoefficientSitePerfect l E X n K) :
    Nonempty ((finiteIntrinsicDerivedTensor l E X n).obj
      ((finiteIntrinsicDerivedInternalHom l E X n).obj
        (op K, (finiteIntrinsicClosed l E X n).monoidal.tensorUnit), L) ≅
      (finiteIntrinsicDerivedInternalHom l E X n).obj (op K, L)) ∧
    ∀ a b c d : ℤ,
      HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1)) K a b →
      HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1)) L c d →
      HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
        ((finiteIntrinsicDerivedInternalHom l E X n).obj (op K, L)) (c - b) (d - a) := by
  classical
  let := integralCoefficientAbSheafify.{u, u} X
  let := integralCoefficientAbLocallyBijective.{u, u} X
  let : ∀ U : X.ProEt, HasSheafify ((ProEt.topology X).over U)
      AddCommGrpCat.{u+1} := fun U ↦ sitePerfectOverAbSheafify.{u, u} X U
  let : ∀ U : X.ProEt, ((ProEt.topology X).over U).WEqualsLocallyBijective
      AddCommGrpCat.{u+1} := fun U ↦ sitePerfectOverAbLocallyBijective.{u, u} X U
  let R : Sheaf (ProEt.topology X) CommRingCat.{u+1} :=
    integralCoefficientCommRingSheaf l E X n
  let C := SheafOfModules.{u+1}
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u+1} RingCat.{u+1})).obj R)
  let := HasDerivedCategory.standard C
  change DerivedCategory C at K L
  let S : CoefficientClosedStructure
      ((finiteIntrinsicDerivedInternalHom l E X n) :
        (DerivedCategory C)ᵒᵖ × DerivedCategory C ⥤ DerivedCategory C) :=
    finiteIntrinsicClosed l E X n
  obtain ⟨M, _, _, hM⟩ := ringedSitePerfectDuality.{u+1, u, u, u+2}
    (ProEt.topology X) R K hK
  let t (P Q : DerivedCategory C) :
      S.tensor.obj (P, Q) ≅ M.closed.tensor.obj (P, Q) :=
    (Adjunction.leftAdjointUniq (S.adjunction Q) (M.closed.adjunction Q)).app P
  let e : S.monoidal.tensorUnit ≅ ringedSiteDualityUnit.{u+1, u, u, u+2} (ProEt.topology X) R :=
    (M.closed.monoidal.rightUnitor S.monoidal.tensorUnit).symm ≪≫
      (t S.monoidal.tensorUnit M.closed.monoidal.tensorUnit).symm ≪≫
      S.monoidal.leftUnitor M.closed.monoidal.tensorUnit ≪≫ M.unitIso
  let d := (finiteIntrinsicDerivedInternalHom l E X n).mapIso
    (Iso.prod (Iso.refl (op K)) e)
  let := hM
  have hi : Nonempty ((finiteIntrinsicDerivedTensor l E X n).obj
      ((finiteIntrinsicDerivedInternalHom l E X n).obj
        (op K, S.monoidal.tensorUnit), L) ≅
      (finiteIntrinsicDerivedInternalHom l E X n).obj (op K, L)) :=
    by
    rw [intrinsic_tensor_eq]
    exact ⟨S.tensor.mapIso (Iso.prod d (Iso.refl L)) ≪≫
      t _ L ≪≫ (asIso (ringedSiteDualEvaluationLeftNatTrans M.closed M.symmetric
        (ringedSiteDualityUnit.{u+1, u, u, u+2} (ProEt.topology X) R) M.unitIso K)).app L⟩
  refine ⟨hi, ?_⟩
  intro a b c d htK htL
  have htD := intrinsic_dual_tor l E X n K hK a b htK
  let O := ringedSiteDualityUnit.{u+1, u, u, u+2} (ProEt.topology X) R
  have ht := intrinsic_tensor_tor l E X n
    ((finiteIntrinsicDerivedInternalHom l E X n).obj (op K, O)) L
    (-b) (-a) c d htD htL
  rw [intrinsic_tensor_eq] at ht
  have he := t ((finiteIntrinsicDerivedInternalHom l E X n).obj (op K, O)) L ≪≫
    (asIso (ringedSiteDualEvaluationLeftNatTrans M.closed M.symmetric O M.unitIso K)).app L
  refine ⟨by have := htK.1; have := htL.1; omega, ?_⟩
  intro G P hG f hf hP N i hidx
  apply ht.2 G P (hG.map (fun j ↦ j ≪≫ he.symm)) f hf hP N i
  rcases hidx with hidx | hidx
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

end WeilConjectures
