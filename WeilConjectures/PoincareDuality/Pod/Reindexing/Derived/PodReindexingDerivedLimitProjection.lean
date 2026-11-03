/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Reindexing.Derived.PodReindexingDerivedCoreData
public import Mathlib.CategoryTheory.Localization.Predicate
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedIntegralFiniteQuotientHomExt
public import WeilConjectures.CategoryTheory.Derived.DerivedExactCube
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.PoincareDuality.Pod.Reindexing.Derived.PodReindexingDerivedReductionEvaluation
public import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingRestrictedTowerNaturality
public import WeilConjectures.SixFunctors.Coefficient.CoefficientActualScalarDerivedPair
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
public import WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels
public import WeilConjectures.SmoothPurity.Supporting.IsomorphismReductionTower

/-! Limit projection law for raw derived comparison data.

The proof constructs the corresponding normalized comparison law from the strict
quotient, evaluation, and Roos-limit calculations.  This is a strictly smaller
obligation than the assembled five-law package.
(blueprint: lem-pod-reindexing-derived-core-limit-projection) -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
  (SY : PodSignedRoosShift (scalarReductionSource l E Y))
  (SX : PodSignedRoosShift (scalarReductionSource l E X))

/-- Derived ordinary restriction square, fixed by localization. -/
private def podReindexingCanonicalRestriction (n : ℕ)
    (s : scalarReductionRestriction l E Y n ⋙ isoReductionIntegralInverse l E g ≅
      isoReductionFiniteInverse l E g n ⋙ scalarReductionRestriction l E X n) :
    coefficientFiniteDerivedRestriction l E Y n ⋙ podOrdinaryReindex l E g ≅
      isoReductionFiniteDerived l E g n ⋙ coefficientFiniteDerivedRestriction l E X n :=
  (mapDerivedCategoryCompIso _ _).symm ≪≫
    mapDerivedCategoryNatIso s ≪≫
    mapDerivedCategoryCompIso _ _

/-- Pointwise transport of a unit square through normalized model comparisons. -/
private theorem normalizedUnitSquare
    {A B C D A₀ B₀ C₀ D₀ : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A₀] [Category B₀] [Category C₀] [Category D₀]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    {QA : A₀ ⥤ A} {QB : B₀ ⥤ B} {QC : C₀ ⥤ C} {QD : D₀ ⥤ D}
    {G₀ : A₀ ⥤ C₀} {H₀ : B₀ ⥤ D₀}
    {R₁₀ : B₀ ⥤ A₀} {R₂₀ : D₀ ⥤ C₀}
    (η₁ : 𝟭 A ⟶ L₁ ⋙ R₁) (η₂ : 𝟭 C ⟶ L₂ ⋙ R₂)
    (ψ : R₁ ⋙ G ≅ H ⋙ R₂) (φ : L₁ ⋙ H ≅ G ⋙ L₂)
    (γ : QA ⋙ G ≅ G₀ ⋙ QC) (θ : QB ⋙ H ≅ H₀ ⋙ QD)
    (ρ₁ : QB ⋙ R₁ ≅ R₁₀ ⋙ QA) (ρ₂ : QD ⋙ R₂ ≅ R₂₀ ⋙ QC)
    (s : R₁₀ ⋙ G₀ ≅ H₀ ⋙ R₂₀)
    (P : A₀) (T : B₀) (V : D₀)
    (c₁ : L₁.obj (QA.obj P) ≅ QB.obj T)
    (c₂ : L₂.obj (QC.obj (G₀.obj P)) ≅ QD.obj V)
    (q : H₀.obj T ≅ V) (u : P ⟶ R₁₀.obj T) (v : G₀.obj P ⟶ R₂₀.obj V)
    (hu : η₁.app (QA.obj P) ≫ R₁.map c₁.hom ≫ ρ₁.hom.app T = QA.map u)
    (hv : η₂.app (QC.obj (G₀.obj P)) ≫ R₂.map c₂.hom ≫ ρ₂.hom.app V = QC.map v)
    (hf : H.map c₁.hom ≫ θ.hom.app T ≫ QD.map q.hom =
      φ.hom.app (QA.obj P) ≫ L₂.map (γ.hom.app P) ≫ c₂.hom)
    (hs : ψ.hom.app (QB.obj T) ≫ R₂.map (θ.hom.app T) ≫ ρ₂.hom.app (H₀.obj T) =
      G.map (ρ₁.hom.app T) ≫ γ.hom.app (R₁₀.obj T) ≫ QC.map (s.hom.app T))
    (ho : G₀.map u ≫ s.hom.app T ≫ R₂₀.map q.hom = v) :
    G.map (η₁.app (QA.obj P)) ≫ ψ.hom.app (L₁.obj (QA.obj P)) =
      η₂.app (G.obj (QA.obj P)) ≫ R₂.map (φ.inv.app (QA.obj P)) := by
  let z := R₂.map (H.map c₁.hom ≫ θ.hom.app T ≫ QD.map q.hom) ≫ ρ₂.hom.app V
  have hz : z = R₂.map (φ.hom.app (QA.obj P)) ≫
      R₂.map (L₂.map (γ.hom.app P)) ≫ R₂.map c₂.hom ≫ ρ₂.hom.app V := by
    dsimp only [z]
    rw [hf]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  have hn := ψ.hom.naturality c₁.hom
  change G.map (R₁.map c₁.hom) ≫ ψ.hom.app (QB.obj T) =
    ψ.hom.app (L₁.obj (QA.obj P)) ≫ R₂.map (H.map c₁.hom) at hn
  have hρ := ρ₂.hom.naturality q.hom
  change R₂.map (QD.map q.hom) ≫ ρ₂.hom.app V =
    ρ₂.hom.app (H₀.obj T) ≫ QC.map (R₂₀.map q.hom) at hρ
  have hg := γ.hom.naturality u
  change G.map (QA.map u) ≫ γ.hom.app (R₁₀.obj T) =
    γ.hom.app P ≫ QC.map (G₀.map u) at hg
  have he := η₂.naturality (γ.hom.app P)
  change γ.hom.app P ≫ η₂.app (QC.obj (G₀.obj P)) =
    η₂.app (G.obj (QA.obj P)) ≫ R₂.map (L₂.map (γ.hom.app P)) at he
  have hμ := congrArg (fun f ↦ G.map f) hu
  simp only [CategoryTheory.Functor.map_comp] at hμ
  apply (cancel_mono z).1
  calc
    (G.map (η₁.app (QA.obj P)) ≫ ψ.hom.app (L₁.obj (QA.obj P))) ≫ z =
        G.map (η₁.app (QA.obj P)) ≫ G.map (R₁.map c₁.hom) ≫
          ψ.hom.app (QB.obj T) ≫ R₂.map (θ.hom.app T) ≫
          R₂.map (QD.map q.hom) ≫ ρ₂.hom.app V := by
      dsimp only [z]
      simp only [CategoryTheory.Functor.map_comp, Category.assoc]
      rw [← reassoc_of% hn]
    _ = G.map (η₁.app (QA.obj P)) ≫ G.map (R₁.map c₁.hom) ≫
          G.map (ρ₁.hom.app T) ≫ γ.hom.app (R₁₀.obj T) ≫
          QC.map (s.hom.app T) ≫ QC.map (R₂₀.map q.hom) := by
      rw [hρ, reassoc_of% hs]
    _ = G.map (QA.map u) ≫ γ.hom.app (R₁₀.obj T) ≫
          QC.map (s.hom.app T) ≫ QC.map (R₂₀.map q.hom) := by
      rw [reassoc_of% hμ]
    _ = γ.hom.app P ≫ QC.map v := by
      rw [reassoc_of% hg]
      have h := congrArg (fun f ↦ γ.hom.app P ≫ QC.map f) ho
      simpa only [CategoryTheory.Functor.map_comp, Category.assoc] using h
    _ = (η₂.app (G.obj (QA.obj P)) ≫ R₂.map (φ.inv.app (QA.obj P))) ≫ z := by
      rw [hz]
      simp only [Category.assoc]
      rw [← R₂.map_comp_assoc, Iso.inv_hom_id_app]
      erw [R₂.map_id, Category.id_comp]
      rw [← reassoc_of% he, hv]

private theorem finiteUnit_model (W : Scheme.{t})
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : integralOperationsGoodComplex l E W P) (n : ℕ) :
    (coefficientFiniteAdjunction l E W n).unit.app (DerivedCategory.Q.obj P) ≫
        (coefficientFiniteDerivedRestriction l E W n).map
          (coefficientFiniteReductionModel l E W P hP.1 n).hom ≫
        (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.hom.app
          (unrestrictedTowerFiniteComplex l E W n P) =
      DerivedCategory.Q.map
        (((scalarReductionExtension_adjunction l E W n).choose.mapHomologicalComplex
          (.up ℤ)).unit.app P) := by
  let s := coefficientActualScalarDerivedPair l E W n
  let _ := s.extension_additive
  let ac := s.ordinaryAdjunction.mapHomologicalComplex (.up ℤ)
  let T := ((s.extension).mapHomologicalComplex (.up ℤ)).obj P
  have h := s.normalization P hP.1 hP.2 T (ac.unit.app P)
  have hu : ac.homEquiv P T (𝟙 _) = ac.unit.app P := by
    rw [Adjunction.homEquiv_unit]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have hi : SheafOfModules.scalarChainTranspose
      (completedIntegralCommRingProjectionUnrestricted l E W n)
      s.extension s.extension_additive s.ordinaryAdjunction P T (ac.unit.app P) = 𝟙 _ := by
    change (ac.homEquiv P T).symm (ac.unit.app P) = 𝟙 _
    rw [← hu]
    exact (ac.homEquiv P T).symm_apply_apply (𝟙 _)
  rw [hi, DerivedCategory.Q.map_id, Category.comp_id] at h
  have hmodel : SheafOfModules.scalarPairComplexComparison
      s.extension s.extension_additive s.derived s.counit P =
      (coefficientFiniteReductionModel l E W P hP.1 n).hom := by
    rfl
  have h' := congrArg (s.adjunction.homEquiv _ _) h
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, hmodel] at h'
  have hfac : (SheafOfModules.scalarRestrictionComparison
      (completedIntegralCommRingProjectionUnrestricted l E W n)).inv.app T =
      (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.inv.app T := rfl
  rw [hfac] at h'
  have h'' := congrArg (fun f ↦ f ≫
    (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.hom.app T) h'
  have he := h''.symm
  simp only [Category.assoc, Iso.inv_hom_id_app] at he
  erw [Category.comp_id] at he
  exact he

private theorem quotient_eq_square
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g)
    (hβ : PodCompletionReindex.QuotientGenerators l E g D)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (hP : integralOperationsGoodComplex l E Y P) (n : ℕ) :
    (D.quotient P hP n).hom =
      ((isoReduction_complexSquare l E g n
        (isoReduction_tensorSquare l E g n).choose).app P).hom := by
  apply HomologicalComplex.Hom.ext
  funext i
  rw [Iso.app_hom, isoReduction_complexSquare_component]
  let a := (isoReduction_tensorSquare l E g n).choose.app (P.X i)
  apply (cancel_epi a.inv).1
  change a.inv ≫ (D.quotient P hP n).hom.f i = a.inv ≫ a.hom
  rw [a.inv_hom_id]
  let R := scalarReductionRestriction l E X n
  have : R.Faithful := by
    constructor
    intro M N f h hf
    ext U x
    exact congrArg (fun k ↦ k.val.app U x) hf
  apply R.map_injective
  apply SheafOfModules.UnrestrictedTowerProof.identified_hom_ext
    (completedIntegralCommRingProjectionUnrestricted l E X n)
    ((isoReductionIntegralInverse l E g).obj (P.X i))
    (scalarReductionExtension l E X n) (isoReduction_extension_obj l E X n) _
  intro V b x
  have hs := isoReduction_tensorSection_eq l E X n
    ((isoReductionIntegralInverse l E g).obj (P.X i)) V b x
  apply (congrArg ((R.map (a.inv ≫ (D.quotient P hP n).hom.f i)).val.app V) hs).trans
  apply Eq.trans _ (congrArg ((R.map (𝟙 _)).val.app V) hs).symm
  let d := isoSectionwiseConstantMap g (CommRingCat.of
    (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))
  let b' := (inv d).hom.app V b
  have hb' : d.hom.app V b' = b :=
    congrArg (fun f ↦ f.hom.app V b) (IsIso.inv_hom_id d)
  have ht := isoReduction_tensorFormula l E g n (isoReduction_tensorSquare l E g n).choose
    (isoReduction_tensorUnit l E g n (isoReduction_tensorSquare l E g n).choose
      (isoReduction_tensorSquare l E g n).choose_spec)
    (P.X i) V b' x
  have hbt := hβ P hP n i V.unop b' x
  rw [hb'] at ht hbt
  change (a.hom.val.app V) _ = _ at ht
  change ((D.quotient P hP n).hom.f i).val.app V _ = _ at hbt
  change ((D.quotient P hP n).hom.f i).val.app V (a.inv.val.app V _) = _
  rw [← ht]
  have ha : a.inv.val.app V (a.hom.val.app V
      (unrestrictedTowerTensorSection l E Y n (P.X i)
        ((proEtaleIsoPostcompose g).op.obj V) b' x)) =
    unrestrictedTowerTensorSection l E Y n (P.X i)
      ((proEtaleIsoPostcompose g).op.obj V) b' x := by
    exact ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.val.app V) a.hom_inv_id) _
  rw [ha]
  exact hbt.trans ht.symm

private theorem finiteUnitTransport
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (s : ∀ n : ℕ,
      scalarReductionRestriction l E Y n ⋙ isoReductionIntegralInverse l E g ≅
        isoReductionFiniteInverse l E g n ⋙ scalarReductionRestriction l E X n)
    (D : PodCompletionReindex l E g)
    (hF : PodCompletionReindex.FiniteModel l E g D)
    (hunit : ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ)
      (hP : integralOperationsGoodComplex l E Y P) (n : ℕ),
      (isoReductionIntegralComplex l E g).map
          (((scalarReductionExtension_adjunction l E Y n).choose.mapHomologicalComplex
            (.up ℤ)).unit.app P) ≫
          (NatTrans.mapHomologicalComplex (s n).hom (.up ℤ)).app
            (unrestrictedTowerFiniteComplex l E Y n P) ≫
          ((scalarReductionRestriction l E X n).mapHomologicalComplex (.up ℤ)).map
            (D.quotient P hP n).hom =
        ((scalarReductionExtension_adjunction l E X n).choose.mapHomologicalComplex
          (.up ℤ)).unit.app ((isoReductionIntegralComplex l E g).obj P))
    (n : ℕ) (K : DerivedCategory (scalarReductionSource l E Y)) :
    (podOrdinaryReindex l E g).map ((coefficientFiniteAdjunction l E Y n).unit.app K) ≫
        (podReindexingCanonicalRestriction l E g n (s n)).hom.app
          ((coefficientFiniteDerivedExtension l E Y n).obj K) =
      (coefficientFiniteAdjunction l E X n).unit.app ((podOrdinaryReindex l E g).obj K) ≫
        (coefficientFiniteDerivedRestriction l E X n).map ((D.finite n).inv.app K) := by
  classical
  let ψ := podReindexingCanonicalRestriction l E g n (s n)
  let left : podOrdinaryReindex l E g ⟶
      coefficientFiniteDerivedExtension l E Y n ⋙ isoReductionFiniteDerived l E g n ⋙
        coefficientFiniteDerivedRestriction l E X n :=
    whiskerRight (coefficientFiniteAdjunction l E Y n).unit (podOrdinaryReindex l E g) ≫
      whiskerLeft (coefficientFiniteDerivedExtension l E Y n) ψ.hom
  let right : podOrdinaryReindex l E g ⟶
      coefficientFiniteDerivedExtension l E Y n ⋙ isoReductionFiniteDerived l E g n ⋙
        coefficientFiniteDerivedRestriction l E X n :=
    whiskerLeft (podOrdinaryReindex l E g) (coefficientFiniteAdjunction l E X n).unit ≫
      whiskerRight (D.finite n).inv (coefficientFiniteDerivedRestriction l E X n)
  have hh : left = right := by
    let ff := Classical.choice (good_whisker_fullyFaithful l E Y
      (DerivedCategory (scalarReductionSource l E X)))
    apply ff.map_injective
    ext P
    change (podOrdinaryReindex l E g).map
        ((coefficientFiniteAdjunction l E Y n).unit.app (DerivedCategory.Q.obj P.obj)) ≫
        ψ.hom.app ((coefficientFiniteDerivedExtension l E Y n).obj
          (DerivedCategory.Q.obj P.obj)) = _
    let T := unrestrictedTowerFiniteComplex l E Y n P.obj
    let FP := (isoReductionIntegralComplex l E g).obj P.obj
    let V := unrestrictedTowerFiniteComplex l E X n FP
    let cY := coefficientFiniteReductionModel l E Y P.obj P.property.1 n
    let cX := coefficientFiniteReductionModel l E X FP (D.good P.obj P.property).1 n
    let q := D.quotient P.obj P.property n
    let aY := (scalarReductionExtension_adjunction l E Y n).choose.mapHomologicalComplex
      (.up ℤ)
    let aX := (scalarReductionExtension_adjunction l E X n).choose.mapHomologicalComplex
      (.up ℤ)
    let sC : (scalarReductionRestriction l E Y n).mapHomologicalComplex (.up ℤ) ⋙
        isoReductionIntegralComplex l E g ≅
      isoReductionFiniteComplex l E g n ⋙
        (scalarReductionRestriction l E X n).mapHomologicalComplex (.up ℤ) :=
      NatIso.ofComponents (fun M ↦ (NatIso.mapHomologicalComplex (s n) (.up ℤ)).app M)
        (by intro M N f; exact (NatIso.mapHomologicalComplex (s n) (.up ℤ)).hom.naturality f)
    have hψ := CategoryTheory.Functor.face_fac
      (scalarReductionRestriction l E Y n) (isoReductionIntegralInverse l E g)
      (isoReductionFiniteInverse l E g n) (scalarReductionRestriction l E X n) (s n) T
    exact normalizedUnitSquare
      (L₁ := coefficientFiniteDerivedExtension l E Y n)
      (R₁ := coefficientFiniteDerivedRestriction l E Y n)
      (L₂ := coefficientFiniteDerivedExtension l E X n)
      (R₂ := coefficientFiniteDerivedRestriction l E X n)
      (G := podOrdinaryReindex l E g) (H := isoReductionFiniteDerived l E g n)
      (QA := DerivedCategory.Q) (QB := DerivedCategory.Q)
      (QC := DerivedCategory.Q) (QD := DerivedCategory.Q)
      (G₀ := isoReductionIntegralComplex l E g)
      (H₀ := isoReductionFiniteComplex l E g n)
      (R₁₀ := (scalarReductionRestriction l E Y n).mapHomologicalComplex (.up ℤ))
      (R₂₀ := (scalarReductionRestriction l E X n).mapHomologicalComplex (.up ℤ))
      (coefficientFiniteAdjunction l E Y n).unit
      (coefficientFiniteAdjunction l E X n).unit ψ (D.finite n)
      (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors
      (isoReductionFiniteInverse l E g n).mapDerivedCategoryFactors
      (scalarReductionRestriction l E Y n).mapDerivedCategoryFactors
      (scalarReductionRestriction l E X n).mapDerivedCategoryFactors sC
      P.obj T V cY cX q (aY.unit.app P.obj) (aX.unit.app FP)
      (finiteUnit_model l E Y P.obj P.property n)
      (finiteUnit_model l E X FP (D.good P.obj P.property) n)
      (hF P.obj P.property n) hψ (hunit P.obj P.property n)
  exact congr_app hh K

private theorem finiteCanonicalProof
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g)
    (hF : PodCompletionReindex.FiniteModel l E g D)
    (hβ : PodCompletionReindex.QuotientGenerators l E g D)
    (n : ℕ) (K : DerivedCategory (scalarReductionSource l E Y)) :
    (podOrdinaryReindex l E g).map ((coefficientFiniteAdjunction l E Y n).unit.app K) ≫
        (podReindexingCanonicalRestriction l E g n
          (isoReduction_restrictionSquare l E g n).choose).hom.app
          ((coefficientFiniteDerivedExtension l E Y n).obj K) =
      (coefficientFiniteAdjunction l E X n).unit.app ((podOrdinaryReindex l E g).obj K) ≫
        (coefficientFiniteDerivedRestriction l E X n).map ((D.finite n).inv.app K) := by
  classical
  apply finiteUnitTransport l E g
    (fun m ↦ (isoReduction_restrictionSquare l E g m).choose) D hF ?_ n K
  intro P hP m
  apply HomologicalComplex.Hom.ext
  funext i
  change (isoReductionIntegralInverse l E g).map
      ((scalarReductionExtension_adjunction l E Y m).choose.unit.app (P.X i)) ≫
      (isoReduction_restrictionSquare l E g m).choose.hom.app
        ((scalarReductionExtension l E Y m).obj (P.X i)) ≫
      (scalarReductionRestriction l E X m).map ((D.quotient P hP m).hom.f i) =
    (scalarReductionExtension_adjunction l E X m).choose.unit.app
      ((isoReductionIntegralInverse l E g).obj (P.X i))
  have hq := congrArg (fun f ↦ f.f i) (quotient_eq_square l E g D hβ P hP m)
  have hqi := hq.trans
    (isoReduction_complexSquare_component l E g m
      (isoReduction_tensorSquare l E g m).choose P i)
  exact (congrArg (fun f ↦
    (isoReductionIntegralInverse l E g).map
        ((scalarReductionExtension_adjunction l E Y m).choose.unit.app (P.X i)) ≫
      (isoReduction_restrictionSquare l E g m).choose.hom.app
        ((scalarReductionExtension l E Y m).obj (P.X i)) ≫
      (scalarReductionRestriction l E X m).map f) hqi).trans
    (by simpa only [isoReduction_adj] using
      (isoReduction_tensorSquare l E g m).choose_spec (P.X i))

private abbrev podReindexingRestrictedComplex (W : Scheme.{t}) (n : ℕ) :=
  (coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ) ⋙
    ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n)).mapHomologicalComplex (.up ℤ)

private def podReindexingRestrictedFactors (W : Scheme.{t}) (n : ℕ) :
    DerivedCategory.Q ⋙ (coefficientSequenceDerivedEvaluation l E W n ⋙
      coefficientFiniteDerivedRestriction l E W n) ≅
    podReindexingRestrictedComplex l E W n ⋙ DerivedCategory.Q :=
  isoWhiskerLeft DerivedCategory.Q (coefficientRestrictedEvaluationIso l E W n).symm ≪≫
    isoWhiskerRight (coefficientSequenceRestriction l E W).mapDerivedCategoryFactors
      (coefficientConstantTowerEvaluation l E W n) ≪≫
    isoWhiskerLeft ((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ))
      (coefficientConstantTowerEvaluationFactors l E W n)

private def podReindexingRestrictedSquareOnComplexes
    (r : ((coefficientSequenceRestriction l E Y).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.complexOfFunctorsToFunctorToComplex) ⋙ podReindexTower l E g ≅
      ((integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ)) ⋙
        ((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.complexOfFunctorsToFunctorToComplex)) (n : ℕ) :
    DerivedCategory.Q ⋙ ((coefficientSequenceDerivedEvaluation l E Y n ⋙
      coefficientFiniteDerivedRestriction l E Y n) ⋙ podOrdinaryReindex l E g) ≅
    DerivedCategory.Q ⋙ (integralComparisonDerivedSequencePullback l E g ⋙
      coefficientSequenceDerivedEvaluation l E X n ⋙ coefficientFiniteDerivedRestriction l E X n) :=
  isoWhiskerRight (podReindexingRestrictedFactors l E Y n) (podOrdinaryReindex l E g) ≪≫
    isoWhiskerLeft (podReindexingRestrictedComplex l E Y n)
      (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors ≪≫
    NatIso.ofComponents
      (F := podReindexingRestrictedComplex l E Y n ⋙
        isoReductionIntegralComplex l E g ⋙ DerivedCategory.Q)
      (G := (integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ) ⋙
        podReindexingRestrictedComplex l E X n ⋙ DerivedCategory.Q)
      (fun C ↦ DerivedCategory.Q.mapIso ((r.app C).app (op n)))
      (by
        intro C D f
        have h := r.hom.naturality f
        have hn := congrArg (fun k ↦ k.app (op n)) h
        simp only [NatTrans.comp_app, Functor.comp_map, podReindexTower,
          Functor.whiskeringRight_obj_map, Functor.whiskerRight_app] at hn
        have hY : (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            ((coefficientSequenceRestriction l E Y).mapHomologicalComplex (.up ℤ) |>.map f)).app
              (op n) =
            (((evaluation ℕᵒᵖ (scalarReductionSource l E Y)).obj (op n)).mapHomologicalComplex
              (.up ℤ)).map
                (((coefficientSequenceRestriction l E Y).mapHomologicalComplex
                  (.up ℤ)).map f)
            := by ext i; rfl
        have hX : (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).map
              (((integralComparisonSequencePullback l E g).mapHomologicalComplex
                    (.up ℤ)).map f))).app
              (op n) =
            (((evaluation ℕᵒᵖ (scalarReductionSource l E X)).obj (op n)).mapHomologicalComplex
              (.up ℤ)).map
                (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).map
                  (((integralComparisonSequencePullback l E g).mapHomologicalComplex
                    (.up ℤ)).map f))
            := by ext i; rfl
        rw [hY, hX] at hn
        simpa only [CategoryTheory.Functor.map_comp, Functor.comp_map, Functor.mapIso_hom,
          Iso.app_hom, podReindexTower, Functor.whiskeringRight_obj_map,
          Functor.whiskerRight_app] using
          congrArg (fun k ↦ DerivedCategory.Q.map k) hn) ≪≫
    (isoWhiskerLeft ((integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ))
      (podReindexingRestrictedFactors l E X n)).symm ≪≫
    (isoWhiskerRight (integralComparisonSequencePullback l E g).mapDerivedCategoryFactors
      (coefficientSequenceDerivedEvaluation l E X n ⋙
        coefficientFiniteDerivedRestriction l E X n)).symm

private theorem projection_surjective (W : Scheme.{t}) (n : ℕ) (U : W.ProEtᵒᵖ) :
    Function.Surjective
      ((completedIntegralCommRingProjectionUnrestricted l E W n).hom.app U) := by
  intro x
  obtain ⟨a, ha⟩ := AlgebraicGeometry.ProEtale.constantQuotient_surjective l E W n U x
  refine ⟨(integralConstantToCompletionOfUniverses l E W).hom.app U a, ?_⟩
  have h := limit.lift_π (integralConstantConeOfUniverses l E W) (op n)
  exact (congrArg (fun f ↦ f.hom.app U a) h).trans ha

private def restrictionFullyFaithful (W : Scheme.{t}) (n : ℕ) :
    (scalarReductionRestriction l E W n).FullyFaithful where
  preimage {M N} f :=
    ⟨{ app := fun U ↦ ModuleCat.ofHom
         { toFun := f.val.app U
           map_add' := map_add _
           map_smul' := fun s x ↦ by
             obtain ⟨a, rfl⟩ := projection_surjective l E W n U s
             exact (f.val.app U).hom.map_smul a x }
       naturality := fun h ↦ by
         ext x
         exact congrArg (fun k ↦ k x) (f.val.naturality h) }⟩
  map_preimage f := by ext U x; rfl
  preimage_map f := by ext U x; rfl

private def restrictedOrdinarySquare (n : ℕ) :
    coefficientSequenceRestriction l E Y ⋙
        (evaluation ℕᵒᵖ (scalarReductionSource l E Y)).obj (op n) ⋙
        isoReductionIntegralInverse l E g ≅
      integralComparisonSequencePullback l E g ⋙ coefficientSequenceRestriction l E X ⋙
        (evaluation ℕᵒᵖ (scalarReductionSource l E X)).obj (op n) :=
  NatIso.ofComponents (fun M ↦ ((restrictedModuleIso l E g).app M).app (op n)) (by
    intro M N f
    exact congrArg (fun k ↦ k.app (op n)) ((restrictedModuleIso l E g).hom.naturality f))

/-- Derive the ordinary evaluation square obtained by canceling scalar restriction.

All map data are explicit. Sectionwise surjectivity supplies only the linearity
proof for the preimage of a restricted module map.
-/
private def podReindexingOrdinaryEvaluation (n : ℕ)
    (s : scalarReductionRestriction l E Y n ⋙ isoReductionIntegralInverse l E g ≅
      isoReductionFiniteInverse l E g n ⋙ scalarReductionRestriction l E X n)
    (rOrd : coefficientSequenceRestriction l E Y ⋙
        (evaluation ℕᵒᵖ (scalarReductionSource l E Y)).obj (op n) ⋙
        isoReductionIntegralInverse l E g ≅
      integralComparisonSequencePullback l E g ⋙ coefficientSequenceRestriction l E X ⋙
        (evaluation ℕᵒᵖ (scalarReductionSource l E X)).obj (op n))
    (hπ : ∀ U : X.ProEtᵒᵖ, Function.Surjective
      ((completedIntegralCommRingProjectionUnrestricted l E X n).hom.app U)) :
    integralComparisonSequencePullback l E g ⋙ coefficientSequenceEvaluation l E X n ≅
      coefficientSequenceEvaluation l E Y n ⋙ isoReductionFiniteInverse l E g n := by
  let ff : (scalarReductionRestriction l E X n).FullyFaithful :=
    { preimage := fun {M N} f ↦
        ⟨{ app := fun U ↦ ModuleCat.ofHom
             { toFun := f.val.app U
               map_add' := map_add _
               map_smul' := fun a x ↦ by
                 obtain ⟨b, rfl⟩ := hπ U a
                 exact (f.val.app U).hom.map_smul b x }
           naturality := fun h ↦ by
             ext x
             exact congrArg (fun k ↦ k x) (f.val.naturality h) }⟩
      map_preimage := fun f ↦ by ext U x; rfl
      preimage_map := fun f ↦ by ext U x; rfl }
  letI := ff.full
  letI := ff.faithful
  let e : (integralComparisonSequencePullback l E g ⋙
        coefficientSequenceEvaluation l E X n) ⋙ scalarReductionRestriction l E X n ≅
      (coefficientSequenceEvaluation l E Y n ⋙ isoReductionFiniteInverse l E g n) ⋙
        scalarReductionRestriction l E X n :=
    isoWhiskerLeft (integralComparisonSequencePullback l E g)
        (eqToIso (coefficientSequenceRestriction_evaluation l E X n)).symm ≪≫
      rOrd.symm ≪≫
      isoWhiskerRight (eqToIso (coefficientSequenceRestriction_evaluation l E Y n))
        (isoReductionIntegralInverse l E g) ≪≫
      isoWhiskerLeft (coefficientSequenceEvaluation l E Y n) s
  exact fullyFaithfulCancelRight (scalarReductionRestriction l E X n) e

/-- Localize the explicitly canceled ordinary evaluation comparison. -/
private def podReindexingCanonicalEvaluation (n : ℕ)
    (s : scalarReductionRestriction l E Y n ⋙ isoReductionIntegralInverse l E g ≅
      isoReductionFiniteInverse l E g n ⋙ scalarReductionRestriction l E X n)
    (rOrd : coefficientSequenceRestriction l E Y ⋙
        (evaluation ℕᵒᵖ (scalarReductionSource l E Y)).obj (op n) ⋙
        isoReductionIntegralInverse l E g ≅
      integralComparisonSequencePullback l E g ⋙ coefficientSequenceRestriction l E X ⋙
        (evaluation ℕᵒᵖ (scalarReductionSource l E X)).obj (op n))
    (hπ : ∀ U : X.ProEtᵒᵖ, Function.Surjective
      ((completedIntegralCommRingProjectionUnrestricted l E X n).hom.app U)) :
    integralComparisonDerivedSequencePullback l E g ⋙
        coefficientSequenceDerivedEvaluation l E X n ≅
      coefficientSequenceDerivedEvaluation l E Y n ⋙ isoReductionFiniteDerived l E g n :=
  (mapDerivedCategoryCompIso _ _).symm ≪≫
    mapDerivedCategoryNatIso (podReindexingOrdinaryEvaluation l E g n s rOrd hπ) ≪≫
      mapDerivedCategoryCompIso _ _

private theorem restrictedFactors_model (W : Scheme.{t}) (n : ℕ)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    (podReindexingRestrictedFactors l E W n).hom.app C ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex
            (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom (.up ℤ)).app C) =
      (coefficientFiniteDerivedRestriction l E W n).map
          ((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app C) ≫
        (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.hom.app
          (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C) := by
  have h := CategoryTheory.Functor.face_fac
    (coefficientSequenceRestriction l E W)
    ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n))
    (coefficientSequenceEvaluation l E W n) (scalarReductionRestriction l E W n)
    (eqToIso (coefficientSequenceRestriction_evaluation l E W n)) C
  change (coefficientRestrictedEvaluationIso l E W n).hom.app
      (DerivedCategory.Q.obj C) ≫ _ = _ at h
  apply (cancel_epi ((coefficientRestrictedEvaluationIso l E W n).hom.app
    (DerivedCategory.Q.obj C))).1
  simp only [podReindexingRestrictedFactors, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]
  erw [Iso.hom_inv_id_app_assoc]
  exact h.symm

private theorem strictSquare_model
    (r : ((coefficientSequenceRestriction l E Y).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.complexOfFunctorsToFunctorToComplex) ⋙ podReindexTower l E g ≅
      ((integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ)) ⋙
        ((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.complexOfFunctorsToFunctorToComplex))
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) (n : ℕ) :
    (podReindexingRestrictedSquareOnComplexes l E g r n).hom.app C ≫
        (isoWhiskerRight (integralComparisonSequencePullback l E g).mapDerivedCategoryFactors
          (coefficientSequenceDerivedEvaluation l E X n ⋙
            coefficientFiniteDerivedRestriction l E X n)).hom.app C ≫
        (isoWhiskerLeft ((integralComparisonSequencePullback l E g).mapHomologicalComplex
          (.up ℤ)) (podReindexingRestrictedFactors l E X n)).hom.app C =
      (podOrdinaryReindex l E g).map
          ((podReindexingRestrictedFactors l E Y n).hom.app C) ≫
        (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app
          ((podReindexingRestrictedComplex l E Y n).obj C) ≫
        DerivedCategory.Q.map ((r.hom.app C).app (op n)) := by
  simp only [podReindexingRestrictedSquareOnComplexes, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  erw [Iso.inv_hom_id_app_assoc
    (isoWhiskerRight (integralComparisonSequencePullback l E g).mapDerivedCategoryFactors
      (coefficientSequenceDerivedEvaluation l E X n ⋙
        coefficientFiniteDerivedRestriction l E X n)) C]
  erw [Iso.inv_hom_id_app
    (isoWhiskerLeft ((integralComparisonSequencePullback l E g).mapHomologicalComplex
      (.up ℤ)) (podReindexingRestrictedFactors l E X n)) C, Category.comp_id]
  simp only [isoWhiskerLeft_hom, isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatIso.ofComponents_hom_app, Functor.mapIso_hom, Iso.app_hom]

private theorem ordinaryEvaluation_square (n : ℕ)
    (s : scalarReductionRestriction l E Y n ⋙ isoReductionIntegralInverse l E g ≅
      isoReductionFiniteInverse l E g n ⋙ scalarReductionRestriction l E X n)
    (rOrd : coefficientSequenceRestriction l E Y ⋙
        (evaluation ℕᵒᵖ (scalarReductionSource l E Y)).obj (op n) ⋙
        isoReductionIntegralInverse l E g ≅
      integralComparisonSequencePullback l E g ⋙ coefficientSequenceRestriction l E X ⋙
        (evaluation ℕᵒᵖ (scalarReductionSource l E X)).obj (op n))
    (hπ : ∀ U : X.ProEtᵒᵖ, Function.Surjective
      ((completedIntegralCommRingProjectionUnrestricted l E X n).hom.app U))
    (M : coefficientSequenceModules l E Y) :
    (isoReductionIntegralInverse l E g).map
        ((eqToIso (coefficientSequenceRestriction_evaluation l E Y n)).hom.app M) ≫
        s.hom.app ((coefficientSequenceEvaluation l E Y n).obj M) =
      rOrd.hom.app M ≫
        (eqToIso (coefficientSequenceRestriction_evaluation l E X n)).hom.app
          ((integralComparisonSequencePullback l E g).obj M) ≫
        (scalarReductionRestriction l E X n).map
          ((podReindexingOrdinaryEvaluation l E g n s rOrd hπ).hom.app M) := by
  let ff := restrictionFullyFaithful l E X n
  let _ := ff.full
  let _ := ff.faithful
  dsimp only [podReindexingOrdinaryEvaluation]
  erw [fullyFaithfulCancelRight_hom_app, (scalarReductionRestriction l E X n).map_preimage]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  erw [Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app_assoc]

private theorem podReindexingCanonicalRestriction_evaluation
    (s : ∀ n : ℕ,
      scalarReductionRestriction l E Y n ⋙ isoReductionIntegralInverse l E g ≅
        isoReductionFiniteInverse l E g n ⋙ scalarReductionRestriction l E X n)
    (rOrd : ∀ n : ℕ, coefficientSequenceRestriction l E Y ⋙
        (evaluation ℕᵒᵖ (scalarReductionSource l E Y)).obj (op n) ⋙
        isoReductionIntegralInverse l E g ≅
      integralComparisonSequencePullback l E g ⋙ coefficientSequenceRestriction l E X ⋙
        (evaluation ℕᵒᵖ (scalarReductionSource l E X)).obj (op n))
    (hπ : ∀ (n : ℕ) (U : X.ProEtᵒᵖ), Function.Surjective
      ((completedIntegralCommRingProjectionUnrestricted l E X n).hom.app U))
    (r : ((coefficientSequenceRestriction l E Y).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.complexOfFunctorsToFunctorToComplex) ⋙ podReindexTower l E g ≅
      (integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ) ⋙
        ((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.complexOfFunctorsToFunctorToComplex))
    (hc : ∀ (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) (n : ℕ) (i : ℤ),
      (((r.hom.app C).app (op n)).f i) = (rOrd n).hom.app (C.X i))
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) (n : ℕ) :
    (podReindexingCanonicalRestriction l E g n (s n)).hom.app
        ((coefficientSequenceDerivedEvaluation l E Y n).obj (DerivedCategory.Q.obj C)) =
      (podReindexingRestrictedSquareOnComplexes l E g r n).hom.app C ≫
        (coefficientFiniteDerivedRestriction l E X n).map
          ((podReindexingCanonicalEvaluation l E g n (s n) (rOrd n) (hπ n)).hom.app
            (DerivedCategory.Q.obj C)) := by
  classical
  let F := isoReductionIntegralInverse l E g
  let H := isoReductionFiniteInverse l E g n
  let RY := scalarReductionRestriction l E Y n
  let RX := scalarReductionRestriction l E X n
  let EY := coefficientSequenceEvaluation l E Y n
  let EX := coefficientSequenceEvaluation l E X n
  let G := integralComparisonSequencePullback l E g
  let T := (EY.mapHomologicalComplex (.up ℤ)).obj C
  let GC := (G.mapHomologicalComplex (.up ℤ)).obj C
  let e := podReindexingOrdinaryEvaluation l E g n (s n) (rOrd n) (hπ n)
  let eC := (NatIso.mapHomologicalComplex e (.up ℤ)).app C
  let aY := (NatIso.mapHomologicalComplex
    (eqToIso (coefficientSequenceRestriction_evaluation l E Y n)) (.up ℤ)).app C
  let aX := (NatIso.mapHomologicalComplex
    (eqToIso (coefficientSequenceRestriction_evaluation l E X n)) (.up ℤ)).app GC
  let sC := (NatIso.mapHomologicalComplex (s n) (.up ℤ)).app T
  let ψ := podReindexingCanonicalRestriction l E g n (s n)
  let δ := podReindexingCanonicalEvaluation l E g n (s n) (rOrd n) (hπ n)
  have ho : (F.mapHomologicalComplex (.up ℤ)).map aY.hom ≫ sC.hom =
      ((r.hom.app C).app (op n)) ≫ aX.hom ≫
        (RX.mapHomologicalComplex (.up ℤ)).map eC.hom := by
    apply HomologicalComplex.Hom.ext
    funext i
    change F.map
        ((eqToIso (coefficientSequenceRestriction_evaluation l E Y n)).hom.app (C.X i)) ≫
        (s n).hom.app (EY.obj (C.X i)) =
      (((r.hom.app C).app (op n)).f i) ≫
        (eqToIso (coefficientSequenceRestriction_evaluation l E X n)).hom.app
          (G.obj (C.X i)) ≫ RX.map (e.hom.app (C.X i))
    conv_rhs => arg 1; rw [hc C n i]
    exact ordinaryEvaluation_square l E g n (s n) (rOrd n) (hπ n) (C.X i)
  have hS := CategoryTheory.Functor.face_fac RY F H RX (s n) T
  change ψ.hom.app (DerivedCategory.Q.obj T) ≫
      RX.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app T) ≫
      RX.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj T) =
    F.mapDerivedCategory.map (RY.mapDerivedCategoryFactors.hom.app T) ≫
      F.mapDerivedCategoryFactors.hom.app ((RY.mapHomologicalComplex (.up ℤ)).obj T) ≫
      DerivedCategory.Q.map sC.hom at hS
  have hE := CategoryTheory.Functor.face_fac G EX EY H e C
  change δ.hom.app (DerivedCategory.Q.obj C) ≫
      H.mapDerivedCategory.map (EY.mapDerivedCategoryFactors.hom.app C) ≫
      H.mapDerivedCategoryFactors.hom.app T =
    EX.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app C) ≫
      EX.mapDerivedCategoryFactors.hom.app GC ≫ DerivedCategory.Q.map eC.hom at hE
  have hY := restrictedFactors_model l E Y n C
  change (podReindexingRestrictedFactors l E Y n).hom.app C ≫
      DerivedCategory.Q.map aY.hom =
    RY.mapDerivedCategory.map (EY.mapDerivedCategoryFactors.hom.app C) ≫
      RY.mapDerivedCategoryFactors.hom.app T at hY
  have hX := restrictedFactors_model l E X n GC
  change (podReindexingRestrictedFactors l E X n).hom.app GC ≫
      DerivedCategory.Q.map aX.hom =
    RX.mapDerivedCategory.map (EX.mapDerivedCategoryFactors.hom.app GC) ≫
      RX.mapDerivedCategoryFactors.hom.app
        ((EX.mapHomologicalComplex (.up ℤ)).obj GC) at hX
  have hR := strictSquare_model l E g r C n
  change (podReindexingRestrictedSquareOnComplexes l E g r n).hom.app C ≫
      RX.mapDerivedCategory.map (EX.mapDerivedCategory.map
        (G.mapDerivedCategoryFactors.hom.app C)) ≫
      (podReindexingRestrictedFactors l E X n).hom.app GC =
    F.mapDerivedCategory.map ((podReindexingRestrictedFactors l E Y n).hom.app C) ≫
      F.mapDerivedCategoryFactors.hom.app ((podReindexingRestrictedComplex l E Y n).obj C) ≫
      DerivedCategory.Q.map ((r.hom.app C).app (op n)) at hR
  have hnψ := ψ.hom.naturality (EY.mapDerivedCategoryFactors.hom.app C)
  change F.mapDerivedCategory.map (RY.mapDerivedCategory.map
      (EY.mapDerivedCategoryFactors.hom.app C)) ≫ ψ.hom.app (DerivedCategory.Q.obj T) =
    ψ.hom.app (EY.mapDerivedCategory.obj (DerivedCategory.Q.obj C)) ≫
      RX.mapDerivedCategory.map (H.mapDerivedCategory.map
        (EY.mapDerivedCategoryFactors.hom.app C)) at hnψ
  have hnF := F.mapDerivedCategoryFactors.hom.naturality aY.hom
  change F.mapDerivedCategory.map (DerivedCategory.Q.map aY.hom) ≫
      F.mapDerivedCategoryFactors.hom.app ((RY.mapHomologicalComplex (.up ℤ)).obj T) =
    F.mapDerivedCategoryFactors.hom.app ((podReindexingRestrictedComplex l E Y n).obj C) ≫
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map aY.hom) at hnF
  have hnRX := RX.mapDerivedCategoryFactors.hom.naturality eC.hom
  change RX.mapDerivedCategory.map (DerivedCategory.Q.map eC.hom) ≫
      RX.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj T) =
    RX.mapDerivedCategoryFactors.hom.app ((EX.mapHomologicalComplex (.up ℤ)).obj GC) ≫
      DerivedCategory.Q.map ((RX.mapHomologicalComplex (.up ℤ)).map eC.hom) at hnRX
  have hδR := congrArg (fun f ↦ RX.mapDerivedCategory.map f) hE
  simp only [CategoryTheory.Functor.map_comp] at hδR
  have hYF := congrArg (fun f ↦ F.mapDerivedCategory.map f) hY
  simp only [CategoryTheory.Functor.map_comp] at hYF
  let z := RX.mapDerivedCategory.map
      (H.mapDerivedCategory.map (EY.mapDerivedCategoryFactors.hom.app C) ≫
        H.mapDerivedCategoryFactors.hom.app T) ≫
      RX.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj T)
  apply (cancel_mono z).1
  calc
    ψ.hom.app (EY.mapDerivedCategory.obj (DerivedCategory.Q.obj C)) ≫ z =
        F.mapDerivedCategory.map ((podReindexingRestrictedFactors l E Y n).hom.app C) ≫
          F.mapDerivedCategoryFactors.hom.app
            ((podReindexingRestrictedComplex l E Y n).obj C) ≫
          DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map aY.hom ≫ sC.hom) := by
      dsimp only [z]
      simp only [CategoryTheory.Functor.map_comp, Category.assoc]
      rw [← reassoc_of% hnψ, hS, ← reassoc_of% hYF, reassoc_of% hnF]
      rw [← DerivedCategory.Q.map_comp]
      rfl
    _ = F.mapDerivedCategory.map ((podReindexingRestrictedFactors l E Y n).hom.app C) ≫
          F.mapDerivedCategoryFactors.hom.app
            ((podReindexingRestrictedComplex l E Y n).obj C) ≫
          DerivedCategory.Q.map (((r.hom.app C).app (op n)) ≫ aX.hom ≫
            (RX.mapHomologicalComplex (.up ℤ)).map eC.hom) := by rw [ho]
    _ = ((podReindexingRestrictedSquareOnComplexes l E g r n).hom.app C ≫
        RX.mapDerivedCategory.map (δ.hom.app (DerivedCategory.Q.obj C))) ≫ z := by
      dsimp only [z]
      simp only [CategoryTheory.Functor.map_comp, Category.assoc]
      rw [reassoc_of% hδR, hnRX, ← reassoc_of% hX, reassoc_of% hR]
      rfl

private abbrev roosProjection (W : Scheme.{t})
    (C : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E W) ℤ) (n : ℕ) :=
  DerivedCategory.Q.map
    (CochainComplex.mappingCocone.fst (podRoosBoundary C) ≫
      Pi.π (fun m : ℕ ↦ C.obj (op m)) n)

private theorem roosProjection_natural (W : Scheme.{t})
    {A B : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E W) ℤ}
    (a : A ⟶ B) (n : ℕ) :
    DerivedCategory.Q.map (integralOperationsRoosFunctor.map a) ≫
        roosProjection l E W B n =
      roosProjection l E W A n ≫ DerivedCategory.Q.map (a.app (op n)) := by
  dsimp only [roosProjection]
  rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
  congr 1
  erw [← Category.assoc, (IntegralAmbient.roosMap_coordinates a).1, Category.assoc,
    Pi.map_π]
  exact (Category.assoc _ _ _).symm

private theorem normalizedRoosProjection (W : Scheme.{t})
    (ρ : IntegralComparisonRoosModel l E W)
    (C : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) (n : ℕ) :
    ρ.comparison.hom.app C ≫ roosProjection l E W C.asFunctor n =
      (coefficientConstantTowerProjection l E W n).app (DerivedCategory.Q.obj C) ≫
        (coefficientConstantTowerEvaluationFactors l E W n).hom.app C := by
  have hi (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
      [I.IsKInjective] :
      ρ.comparison.hom.app I ≫ roosProjection l E W I.asFunctor n =
        (coefficientConstantTowerProjection l E W n).app (DerivedCategory.Q.obj I) ≫
          (coefficientConstantTowerEvaluationFactors l E W n).hom.app I := by
    rw [ρ.computes I]
    dsimp only [roosProjection]
    rw [Category.assoc, ← DerivedCategory.Q.map_comp]
    have h := (integralComparisonLimitToRoos_existsUnique l E W I).exists.choose_spec.1 n
    change integralComparisonLimitToRoos l E W I ≫ _ ≫ _ = _ at h
    rw [h]
    exact ((coefficientConstantTowerProjection_exists l E W n).choose_spec.1 I).symm
  obtain ⟨I, hI, f, _, hf⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective C
  have : QuasiIso f := hf
  let V := (evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n)
  apply (cancel_mono (DerivedCategory.Q.map
    ((V.mapHomologicalComplex (.up ℤ)).map f))).1
  have hv := V.mapDerivedCategoryFactors.hom.naturality f
  have hp := (coefficientConstantTowerProjection l E W n).naturality
    (DerivedCategory.Q.map f)
  have hθ := ρ.comparison.hom.naturality f
  dsimp only [Functor.comp_map] at hv hθ
  erw [Category.assoc, ← roosProjection_natural l E W
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f) n]
  rw [← Category.assoc, ← hθ, Category.assoc]
  erw [hi I]
  rw [Category.assoc, ← hv]
  exact (reassoc_of% hp) _

private theorem podReindexingRestrictedFactors_projection (W : Scheme.{t})
    (ρ : IntegralComparisonRoosModel l E W)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) (n : ℕ) :
    (podLimitRoos l E ρ C).hom ≫ roosProjection l E W (podRestrictedTower l E C) n =
      (coefficientSequenceProjection l E W n).app (DerivedCategory.Q.obj C) ≫
        (podReindexingRestrictedFactors l E W n).hom.app C := by
  dsimp only [podLimitRoos, Iso.trans_hom, Functor.mapIso_hom]
  erw [Category.assoc, normalizedRoosProjection l E W ρ
    (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C) n]
  unfold coefficientSequenceProjection podReindexingRestrictedFactors
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Category.assoc,
    Iso.hom_inv_id_app_assoc, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    Functor.whiskerRight_app]
  erw [reassoc_of% ((coefficientConstantTowerProjection l E W n).naturality
    ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.hom.app C))]

private theorem reindexRoosProjection (S : PodReindexingStrictData l E g)
    (hS : S.RoosFst l E g)
    (C : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E Y) ℤ) (n : ℕ) :
    DerivedCategory.Q.map (S.roos C).hom ≫
        roosProjection l E X ((podReindexTower l E g).obj C) n =
      DerivedCategory.Q.map ((isoReductionIntegralComplex l E g).map
        (CochainComplex.mappingCocone.fst (podRoosBoundary C) ≫
          Pi.π (fun m : ℕ ↦ C.obj (op m)) n)) := by
  dsimp only [roosProjection]
  rw [← DerivedCategory.Q.map_comp]
  congr 1
  rw [← Category.assoc, hS C, Category.assoc, podReindexProduct, Pi.lift_π]
  exact ((isoReductionIntegralComplex l E g).map_comp _ _).symm

private theorem projectionOnComplexes
    (S : PodReindexingStrictData l E g) (hS : S.Laws l E g SY SX)
    (D : PodCompletionReindex l E g)
    (hL : PodCompletionReindex.LimitModel l E g D)
    (hroos : D.roos = S.roos) (hrest : D.restricted = S.restricted)
    (r : ((coefficientSequenceRestriction l E Y).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.complexOfFunctorsToFunctorToComplex) ⋙ podReindexTower l E g ≅
      ((integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ)) ⋙
        ((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.complexOfFunctorsToFunctorToComplex))
    (hr : ∀ C, S.restricted C = r.app C)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) (n : ℕ) :
    (podOrdinaryReindex l E g).map
        ((coefficientSequenceProjection l E Y n).app (DerivedCategory.Q.obj C)) ≫
        (podReindexingRestrictedSquareOnComplexes l E g r n).hom.app C =
      D.limit.hom.app (DerivedCategory.Q.obj C) ≫
        (coefficientSequenceProjection l E X n).app
          ((integralComparisonDerivedSequencePullback l E g).obj (DerivedCategory.Q.obj C)) := by
  let G := integralComparisonSequencePullback l E g
  let H := coefficientSequenceDerivedEvaluation l E X n ⋙
    coefficientFiniteDerivedRestriction l E X n
  let GC := G.mapHomologicalComplex (.up ℤ)
  apply (cancel_mono
    ((isoWhiskerRight G.mapDerivedCategoryFactors H).hom.app C ≫
      (isoWhiskerLeft GC (podReindexingRestrictedFactors l E X n)).hom.app C)).1
  simp only [podReindexingRestrictedSquareOnComplexes, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  erw [Iso.inv_hom_id_app_assoc (isoWhiskerRight G.mapDerivedCategoryFactors H) C]
  erw [Iso.inv_hom_id_app (isoWhiskerLeft GC (podReindexingRestrictedFactors l E X n)) C,
    Category.comp_id]
  simp only [isoWhiskerLeft_hom, isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatIso.ofComponents_hom_app, Functor.mapIso_hom, Iso.app_hom]
  erw [← (coefficientSequenceProjection l E X n).naturality_assoc]
  erw [← podReindexingRestrictedFactors_projection l E X D.targetRoos]
  have h := congrArg (fun f ↦ f ≫ roosProjection l E X
    (podRestrictedTower l E (GC.obj C)) n) (hL C)
  rw [hroos, hrest] at h
  simp only [Category.assoc] at h
  erw [roosProjection_natural l E X (S.restricted C).hom n] at h
  erw [reassoc_of% (reindexRoosProjection l E g S hS.1
    (podRestrictedTower l E C) n)] at h
  rw [hr C] at h
  rw [← h]
  let p : integralOperationsRoos (A := scalarReductionSource l E Y)
      (podRestrictedTower l E C) ⟶
      (podRestrictedTower l E C).obj (op n) :=
    CochainComplex.mappingCocone.fst
        (podRoosBoundary (A := scalarReductionSource l E Y) (podRestrictedTower l E C)) ≫
      Pi.π (fun m : ℕ ↦ (podRestrictedTower l E C).obj (op m)) n
  have hf := (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.naturality p
  dsimp only [Functor.comp_map, p] at hf
  erw [← reassoc_of% hf]
  change _ = (podOrdinaryReindex l E g).map (podLimitRoos l E D.sourceRoos C).hom ≫
    (podOrdinaryReindex l E g).map (roosProjection l E Y (podRestrictedTower l E C) n) ≫
    (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app
      ((podReindexingRestrictedComplex l E Y n).obj C) ≫
        DerivedCategory.Q.map ((r.hom.app C).app (op n))
  simp only [← (podOrdinaryReindex l E g).map_comp_assoc]
  erw [podReindexingRestrictedFactors_projection l E Y D.sourceRoos]

/-- Choose evaluation and restriction jointly with both projection and finite adjunction.

STATEMENT-DISPUTED: the former arbitrary raw-data statement has independent limit,
evaluation and restriction maps, so does not imply its projection equation. The earlier
existential restriction repair alone also conflicts with the finite adjoint mate.

Source: strict restricted-tower comparison, normalized scalar adjunction, and the first
Roos coordinate. Choose the canonical ordinary restriction square and a compatible
derived evaluation square. Its normalization on complexes turns the full Roos-model
identity into the projection identity. Fully faithful localization extends the identity
to every derived system. The finite-model normalization makes this same restriction the
finite adjoint mate. The two unit/projection equations then imply reduction evaluation
by the adjunction bijection. Only evaluation and restriction change: finite, reduction,
limit and both Roos models are retained verbatim, so the parent's finite, limit and unit
laws still apply to the jointly chosen record.
(blueprint: lem-pod-reindexing-derived-core-limit-projection) -/
theorem podReindexingDerivedCoreData_limitProjection
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (S : PodReindexingStrictData l E g) (hS : S.Laws l E g SY SX)
    (β : ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ),
      integralOperationsGoodComplex l E Y P → ∀ n : ℕ,
      (isoReductionFiniteComplex l E g n).obj (unrestrictedTowerFiniteComplex l E Y n P) ≅
        unrestrictedTowerFiniteComplex l E X n
          ((isoReductionIntegralComplex l E g).obj P))
    (hβ : podReindexingCoreQuotientGenerators l E g β)
    (htransition : podReindexingCoreQuotientTransition l E g β)
    (CY : IntegralOnSlice.completion l E Y none ≅
      (podReindexCalculus l E Y).reduction ⋙ coefficientSequenceLimit l E Y)
    (CX : IntegralOnSlice.completion l E X none ≅
      (podReindexCalculus l E X).reduction ⋙ coefficientSequenceLimit l E X)
    (Q : PodReindexingDerivedCoreData l E g)
    (hF : PodCompletionReindex.FiniteModel l E g
      (Q.assemble l E g SY SX S β CY CX))
    (hL : PodCompletionReindex.LimitModel l E g
      (Q.assemble l E g SY SX S β CY CX)) :
    ∃ δ : ∀ n : ℕ, integralComparisonDerivedSequencePullback l E g ⋙
        coefficientSequenceDerivedEvaluation l E X n ≅
      coefficientSequenceDerivedEvaluation l E Y n ⋙ isoReductionFiniteDerived l E g n,
    ∃ ψ : ∀ n : ℕ, coefficientFiniteDerivedRestriction l E Y n ⋙
        podOrdinaryReindex l E g ≅
      isoReductionFiniteDerived l E g n ⋙ coefficientFiniteDerivedRestriction l E X n,
      let Q' : PodReindexingDerivedCoreData l E g :=
        { Q with evaluation := δ, restriction := ψ }
      PodCompletionReindex.LimitProjection l E g
        (Q'.assemble l E g SY SX S β CY CX) ∧
      (PodCompletionReindex.Unit l E g (Q'.assemble l E g SY SX S β CY CX) →
        PodCompletionReindex.ReductionEvaluation l E g
          (Q'.assemble l E g SY SX S β CY CX)) := by
  classical
  let D := Q.assemble l E g SY SX S β CY CX
  let s := fun n ↦ (isoReduction_restrictionSquare l E g n).choose
  have hm := finiteCanonicalProof l E g D hF hβ
  let rOrd := restrictedOrdinarySquare l E g
  let r := restrictedIso l E g
  have hr := restricted_eq l E g S hS.2.2.2.2
  have hc : ∀ (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) (n : ℕ) (i : ℤ),
      (((r.hom.app C).app (op n)).f i) = (rOrd n).hom.app (C.X i) := by
    intro C n i
    rfl
  let hπ := fun n U ↦ projection_surjective l E X n U
  let δ := fun n ↦ podReindexingCanonicalEvaluation l E g n (s n) (rOrd n) (hπ n)
  have hcompat := podReindexingCanonicalRestriction_evaluation l E g s rOrd hπ r hc
  let ψ := fun n ↦ podReindexingCanonicalRestriction l E g n (s n)
  let Q' : PodReindexingDerivedCoreData l E g :=
    { Q with evaluation := δ, restriction := ψ }
  have hp : PodCompletionReindex.LimitProjection l E g
      (Q'.assemble l E g SY SX S β CY CX) := by
    intro A n
    let left : coefficientSequenceLimit l E Y ⋙ podOrdinaryReindex l E g ⟶
        coefficientSequenceDerivedEvaluation l E Y n ⋙
          isoReductionFiniteDerived l E g n ⋙ coefficientFiniteDerivedRestriction l E X n :=
      whiskerRight (coefficientSequenceProjection l E Y n) (podOrdinaryReindex l E g) ≫
        whiskerLeft (coefficientSequenceDerivedEvaluation l E Y n) (ψ n).hom
    let right : coefficientSequenceLimit l E Y ⋙ podOrdinaryReindex l E g ⟶
        coefficientSequenceDerivedEvaluation l E Y n ⋙
          isoReductionFiniteDerived l E g n ⋙ coefficientFiniteDerivedRestriction l E X n :=
      Q.limit.hom ≫ whiskerLeft (integralComparisonDerivedSequencePullback l E g)
        (coefficientSequenceProjection l E X n) ≫
          whiskerRight (δ n).hom (coefficientFiniteDerivedRestriction l E X n)
    have he : left = right := by
      let fq := Localization.fullyFaithfulWhiskeringLeft
        (DerivedCategory.Q (C := coefficientSequenceModules l E Y))
        (HomologicalComplex.quasiIso (coefficientSequenceModules l E Y) (.up ℤ))
        (DerivedCategory (scalarReductionSource l E X))
      apply fq.map_injective
      ext C
      change (podOrdinaryReindex l E g).map
          ((coefficientSequenceProjection l E Y n).app (DerivedCategory.Q.obj C)) ≫
          (ψ n).hom.app ((coefficientSequenceDerivedEvaluation l E Y n).obj
            (DerivedCategory.Q.obj C)) = _
      rw [hcompat C n]
      change _ = Q.limit.hom.app (DerivedCategory.Q.obj C) ≫
        (coefficientSequenceProjection l E X n).app
          ((integralComparisonDerivedSequencePullback l E g).obj (DerivedCategory.Q.obj C)) ≫
        (coefficientFiniteDerivedRestriction l E X n).map
          ((δ n).hom.app (DerivedCategory.Q.obj C))
      have hc := projectionOnComplexes l E g SY SX S hS D hL rfl rfl r hr C n
      dsimp only [D, PodReindexingDerivedCoreData.assemble] at hc
      simpa only [δ, Functor.comp_obj, Category.assoc] using congrArg
        (fun f ↦ f ≫ (coefficientFiniteDerivedRestriction l E X n).map
          ((δ n).hom.app (DerivedCategory.Q.obj C))) hc
    exact congr_app he A
  refine ⟨δ, ψ, hp, ?_⟩
  intro hu K n
  exact evaluationOfUnits _ _ _ _ _ _ _ _ _ _ _ _ _
    (podReindexCalculus l E Y).adjunction (podReindexCalculus l E X).adjunction
    (coefficientFiniteAdjunction l E Y n) (coefficientFiniteAdjunction l E X n)
    ((podReindexCalculus l E Y).reductionEvaluation n)
    ((podReindexCalculus l E X).reductionEvaluation n)
    (coefficientSequenceProjection l E Y n) (coefficientSequenceProjection l E X n)
    Q.reduction Q.limit (δ n) (Q.finite n) (ψ n)
    (fun K ↦ (podReindexCalculus l E Y).unit_projection K n)
    (fun K ↦ (podReindexCalculus l E X).unit_projection K n)
    (hm n) hu (fun N ↦ hp N n) K

end WeilConjectures
