/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.IntegralCompletedComparison.IntegralPullbackCompletedComparisonData
public import WeilConjectures.DeligneLaumon.FinitePullbackStrictTower.FinitePullbackStrictTowerComparison
import WeilConjectures.CategoryTheory.DeligneLaumon.CompletedRlimRoosComparison
import WeilConjectures.DeligneLaumon.IntegralCompletedComparison.IntegralRoosFiniteTowerShift
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement


/-! # Integral Roos realization through the finite-tower derived pair

Source: Stacks Project, sites-cohomology.tex, Tag 0941, and proetale.tex, Tag 099N(5).
(blueprint: lem-a1-integral-roos-finite-tower-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.IntegralOnSlice.hasDerived
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
  WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
  WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
attribute [local irreducible] HasDerivedCategory.standard CategoryTheory.constantSheaf
attribute [local implicit_reducible] SheafOfModules.instAbelian
  CategoryTheory.abelianOfAdjunction CategoryTheory.Abelian.ofCoimageImageComparisonIsIso
  WeilConjectures.scalarReductionSourceDerived WeilConjectures.scalarReductionTargetDerived
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.integralTowerHasDerivedCategory
  WeilConjectures.integralCompletedRingHasDerivedCategory
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
private instance (priority := 6000) fixedAbSheafify (W : Scheme.{u}) :
    HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} W
private instance (priority := 6000) fixedAbBijective (W : Scheme.{u}) :
    (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} W
namespace WeilConjectures.IntegralCompletedComparison
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- Total derived limit of the normalized finite pullback derived pair.
Source: Stacks 0941, 099N(5)
(blueprint: lem-a1-integral-roos-finite-tower-realization). -/
abbrev finiteTowerLimit (C : FinitePullbackStrictTower.Comparison.{u, u} l E g) :=
  (derived.{u} l E Y ⋙ C.B.functor) ⋙
    completedRlim.{u} X (completedIntegralCommRingSheafUnrestricted.{u, u} l E X)

/-- Its shift uses the retained finite-tower shift and the standard total-limit shift.
Source: Stacks 014E, 0941
(blueprint: lem-a1-integral-roos-finite-tower-realization). -/
instance finiteTowerLimit_commShift
    (C : FinitePullbackStrictTower.Comparison.{u, u} l E g) :
    (finiteTowerLimit l E g C).CommShift ℤ := by
  letI := C.finiteShift
  infer_instance

/-- The nth projection through the actual finite-tower computation counit.
The first factor accounts for exact completed-coefficient restriction on P.
Source: Stacks 0941, universal derived-limit projections
(blueprint: lem-a1-integral-roos-finite-tower-realization). -/
def finiteTowerLimitProjection (C : FinitePullbackStrictTower.Comparison.{u, u} l E g)
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l E))) ℤ)
    (n : ℕ) :
    (finiteTowerLimit l E g C).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((integralOperationsPullbackTowerFunctor.{u, u} l E g).obj
          ((complexes l E Y).obj P)).obj (op n)) :=
  (completedRlim.{u} X (completedIntegralCommRingSheafUnrestricted.{u, u} l E X)).map
      (C.B.functor.map ((modules l E Y).mapDerivedCategoryFactors.hom.app P) ≫
        C.B.counit.app ((complexes l E Y).obj P)) ≫
    (completedRlimProjection.{u} X (completedIntegralCommRingSheafUnrestricted.{u, u} l E X) n).app
      (DerivedCategory.Q.obj
        ((FinitePullbackStrictTower.finiteComplex.{u, u} l E g).obj
          ((complexes l E Y).obj P))) ≫
    (((evaluation ℕᵒᵖ (reductionModules X
        (completedIntegralCommRingSheafUnrestricted.{u, u} l E X))).obj
          (op n)).mapDerivedCategoryFactors.hom.app
        ((FinitePullbackStrictTower.finiteComplex.{u, u} l E g).obj
          ((complexes l E Y).obj P)))

private abbrev rlim :=
  completedRlim.{u} X (completedIntegralCommRingSheafUnrestricted.{u, u} l E X)

private theorem integralCofiberMap_eq_coneMap
    {V : Type*} [Category V] [Abelian V]
    {K L K' L' : CochainComplex V ℤ} (f : K ⟶ L) (g : K' ⟶ L')
    (a : K ⟶ K') (b : L ⟶ L') (h : a ≫ g = f ≫ b) :
    HomologicalComplex.homotopyCofiber.mapArrowHom f g
      (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) (Arrow.homMk a b h) =
      CochainComplex.mappingCone.map f g a b h.symm := by
  ext i
  apply HomologicalComplex.homotopyCofiber.ext_from_X f (i + 1) i rfl
  all_goals simp [HomologicalComplex.homotopyCofiber.mapArrowHom,
    HomologicalComplex.homotopyCofiber.desc_f,
    HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom,
    CochainComplex.mappingCone.map, CochainComplex.mappingCone.desc,
    CochainComplex.mappingCone.descCochain, CochainComplex.HomComplex.Cochain.comp_v,
    CochainComplex.mappingCone.inl, CochainComplex.mappingCone.fst,
    CochainComplex.mappingCone.snd, CochainComplex.mappingCone.inr]


private def roosTransposeIso
    {A : Type*} [Category* A] [Abelian A] [HasCountableProducts A] :
    integralOperationsRoosFunctor (A := A) ≅
      (HomologicalComplex.functorEquivalence A (.up ℤ) ℕᵒᵖ).inverse ⋙ roosF :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro P Q f
    dsimp only [Iso.refl_hom]
    rw [Category.comp_id, Category.id_comp]
    dsimp only [integralOperationsRoosFunctor, integralOperationsRoosMap,
      Functor.comp_map, roosF, roosConeFunctor]
    rw [integralCofiberMap_eq_coneMap]
    rfl)

private def goodFiniteComparison
    (C : FinitePullbackStrictTower.Comparison.{u, u} l E g)
    (e : roosF (A := integralTowerModules.{u, u} l E X) ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q ⋙ rlim l E (X := X)) :
    integralOperationsGoodLocalization.{u, u} l E Y ⋙ (C.B.functor ⋙ rlim l E (X := X)) ≅
      integralOperationsPullbackOnGood.{u, u} l E g := by
  let G := integralOperationsGoodComplex.{u, u} l E Y
  let η := Functor.whiskerLeft G.ι C.B.counit
  have (P : G.FullSubcategory) : IsIso (η.app P) :=
    C.B.computes P.obj P.property
  have : IsIso η := NatIso.isIso_of_isIso_app η
  exact Functor.isoWhiskerRight (asIso η) (rlim l E (X := X)) ≪≫
    Functor.isoWhiskerLeft (G.ι ⋙ FinitePullbackStrictTower.finiteComplex l E g) e.symm ≪≫
      (Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft (G.ι ⋙ integralOperationsPullbackTowerFunctor l E g)
          roosTransposeIso) DerivedCategory.Q).symm

private theorem descentComparison
    (C : FinitePullbackStrictTower.Comparison.{u, u} l E g)
    (e : roosF (A := integralTowerModules.{u, u} l E X) ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q ⋙ rlim l E (X := X)) :
    ∃ b : integralDerivedPullback.{u, u} l E g ≅ C.B.functor ⋙ rlim l E (X := X),
      Functor.isoWhiskerLeft (integralOperationsGoodLocalization l E Y) b ≪≫
        goodFiniteComparison l E g C e = integralDerivedPullbackComparison l E g := by
  exact ((integralPullbackDescent l E g).universal _
    (goodFiniteComparison l E g C e)).exists

/-- The integral Roos construction realizes the total derived limit of its finite
pullback tower. This concerns the integral presentation alone, on every input;
it neither compares coefficient presentations nor uses intrinsic completeness.
Source: Stacks Project, sites-cohomology.tex, Tag 0941; proetale.tex, Tag 099N(5)
(blueprint: lem-a1-integral-roos-finite-tower-realization).
Proof: on a good representative P, the counit of C.B identifies its derived
finite tower with the localization of the actual strict finite pullback tower.
Transpose this tower to a complex of towers. Exact countable products give the
normalized strict Roos isomorphism from its product mapping fibre to the total
right derived inverse limit. Compose with the inverse of the limit of C.B's
counit. Both constructions are natural on good representatives. Their resolving
localization is fully faithful on functor categories, so the isomorphism descends
uniquely to the given integral pullback. The normalization on K-injective tower
resolutions identifies every projection with the first mapping-cocone coordinate
followed by the corresponding product leg. Apply this before and after the exact
coefficient restriction computation map to obtain the displayed equation for
all good P. The normalized Roos shift theorem gives the signed product-fibre shift;
C.finiteShift_descent and ShiftDescent identify its two descents, giving precisely
the CommShift equation, including the zero and addition laws. -/
theorem integralPullback_roosFiniteTower
    (C : FinitePullbackStrictTower.Comparison.{u, u} l E g)
    (c : (integralOperationsPullbackComplexFunctor.{u, u} l E g).CommShift ℤ)
    (hc : ShiftCoordinates l E g c)
    (d : (integralDerivedPullback.{u, u} l E g).CommShift ℤ)
    (hd : ShiftDescent l E g c d) :
    ∃ a : integral l E g ≅ finiteTowerLimit l E g C,
      (∀ (P : CochainComplex
          (pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l E))) ℤ)
        (hP : integralOperationsGoodComplex.{u, u} l E Y ((complexes l E Y).obj P))
        (n : ℕ),
        a.hom.app (DerivedCategory.Q.obj P) ≫ finiteTowerLimitProjection l E g C P n =
          integralProjection l E g P hP n) ∧
      (fun [_d : (integralDerivedPullback.{u, u} l E g).CommShift ℤ] ↦
        NatTrans.CommShift a.hom ℤ) (_d := d) := by
  have : HasExactLimitsOfShape (Discrete ℕ) (integralTowerModules.{u, u} l E X) :=
    integralOperationsExactProducts l E X
  obtain ⟨e, he, heπ⟩ := completedRlim_roosComparison X
    (completedIntegralCommRingSheafUnrestricted.{u, u} l E X)
  obtain ⟨b, hb⟩ := descentComparison l E g C e
  have hb' (P : CochainComplex (integralTowerModules.{u, u} l E Y) ℤ)
      (hP : integralOperationsGoodComplex.{u, u} l E Y P) :
      b.hom.app (DerivedCategory.Q.obj P) ≫
          (rlim l E (X := X)).map (C.B.counit.app P) =
        (integralDerivedPullbackComparison.{u, u} l E g).hom.app ⟨P, hP⟩ ≫
          e.hom.app ((FinitePullbackStrictTower.finiteComplex.{u, u} l E g).obj P) := by
    have h := congrArg (fun z ↦ z.hom.app ⟨P, hP⟩) hb
    dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, goodFiniteComparison, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, asIso_hom, Iso.symm_hom, Iso.trans_inv,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, asIso_inv] at h
    have h' := congrArg (fun f ↦ f ≫
      e.hom.app ((FinitePullbackStrictTower.finiteComplex.{u, u} l E g).obj P)) h
    simp only [roosTransposeIso, NatIso.ofComponents_inv_app, Iso.refl_inv] at h'
    erw [CategoryTheory.Functor.map_id] at h'
    simp only [Category.assoc] at h'
    erw [Category.id_comp, Iso.inv_hom_id_app, Category.comp_id] at h'
    exact h'
  let a : integral l E g ≅ finiteTowerLimit l E g C :=
    Functor.isoWhiskerLeft (derived l E Y) b ≪≫
      (Functor.associator (derived l E Y) C.B.functor (rlim l E (X := X))).symm
  refine ⟨a, ?_, ?_⟩
  · intro P hP n
    have hn := heπ ((FinitePullbackStrictTower.finiteComplex l E g).obj
      ((complexes l E Y).obj P)) n
    have hbP := hb' ((complexes l E Y).obj P) hP
    have hnat := b.hom.naturality ((modules l E Y).mapDerivedCategoryFactors.hom.app P)
    dsimp only [a, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.associator_inv_app,
      finiteTowerLimitProjection, integralProjection, integralComputation]
    dsimp only [Functor.comp_map] at hnat
    simp only [Category.comp_id, Functor.map_comp, Category.assoc]
    erw [← reassoc_of% hnat, reassoc_of% hbP, hn]
    simp only [roosEval, Functor.map_comp]
    rfl
  · let := C.finiteShift
    let := d
    have hshift : NatTrans.CommShift b.hom ℤ :=
      integralRoosFiniteTower_commShift l E g C e he b hb' c hc d hd
    dsimp only [a, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom]
    infer_instance

end WeilConjectures.IntegralCompletedComparison
