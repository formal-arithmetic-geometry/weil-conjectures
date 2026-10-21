/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.CategoryTheory.FlatScalarKoszulModels
public import Sheaf.CategoryTheory.RingedKoszulSystem
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import Sheaf.Paper.RestrictionDerivedProducts
public import Sheaf.Paper.RingedTopoiTensorSections
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.CategoryTheory.StrictScalarKoszulComparison
import Sheaf.CategoryTheory.RingedCechKoszulComparisonOnSite
import all Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses

/-! # Flat scalar restriction of the strict Koszul tower

Source: Stacks Project, algebraization.tex, Tag 0A0E; sites-cohomology.tex, Tags 0A07
and 0941; more-algebra.tex, Tag 0913.
(blueprint: lem-weil-pbc-flat-scalar-koszul-tower-comparison).

## Main statements

* `flatScalarKoszulTowerComparison`: strict and derived normalized comparisons.

The coordinate maps below use the ordered tensor basis of the positive Koszul complex,
its dual evaluation, and the coproduct maps of total tensor. They specify actual maps,
so the comparison cannot be changed by a simultaneous choice of coordinates.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory.FlatScalarKoszul

variable {S : Type u} [SmallCategory S] {J : GrothendieckTopology S}

variable {R B : Sheaf J CommRingCat.{u}}
variable [HasDerivedCategory.{w} (Modules R)] [HasDerivedCategory.{w} (Modules B)]
variable [HasDerivedCategory.{w} (Towers R)] [HasDerivedCategory.{w} (Towers B)]

/-- Exact scalar restriction on unbounded derived categories. Source: Stacks 0A07
(blueprint: lem-weil-pbc-flat-scalar-koszul-tower-comparison). -/
abbrev restrictDerived (φ : R ⟶ B) := (restriction φ).mapDerivedCategory

/-- Exact levelwise scalar restriction on the derived category of strict towers.
Source: Stacks 0A07
(blueprint: lem-weil-pbc-flat-scalar-koszul-tower-comparison). -/
abbrev restrictTowerDerived (φ : R ⟶ B) := (restrictTower φ).mapDerivedCategory

/-- Exact evaluation on the derived category of strict towers. Source: Stacks 0941
(blueprint: lem-weil-pbc-flat-scalar-koszul-tower-comparison). -/
abbrev evaluateDerived (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules O)] [HasDerivedCategory.{w} (Towers O)]
    (m : ℕᵒᵖ) := ((evaluation ℕᵒᵖ (Modules O)).obj m).mapDerivedCategory

/-- Restriction and evaluation commute by the exact-functor localization comparisons.
Source: Stacks 0A07
(blueprint: lem-weil-pbc-flat-scalar-koszul-tower-comparison). -/
def evaluationComparison (φ : R ⟶ B) (m : ℕᵒᵖ) :
    restrictTowerDerived φ ⋙ evaluateDerived R m ≅
      evaluateDerived B m ⋙ restrictDerived φ :=
  (Functor.mapDerivedCategoryCompIso (restrictTower φ)
    ((evaluation ℕᵒᵖ (Modules R)).obj m)).symm ≪≫
      Functor.mapDerivedCategoryCompIso ((evaluation ℕᵒᵖ (Modules B)).obj m) (restriction φ)

/-- The canonical ordinary inverse-limit projection, applied degreewise.
Source: Stacks 0941
(blueprint: lem-weil-pbc-flat-scalar-koszul-tower-comparison). -/
abbrev limitProjection (O : Sheaf J CommRingCat.{u}) (m : ℕᵒᵖ) :=
  NatTrans.mapHomologicalComplex
    (lim.π m : (lim : Towers O ⥤ Modules O) ⟶ (evaluation ℕᵒᵖ (Modules O)).obj m) (.up ℤ)

private theorem inverseUnitComparison
    {A' B' : Type*} [Category A'] [Category B']
    {LA : A' ⥤ A'} {LB : B' ⥤ B'}
    (uA : 𝟭 A' ⟶ LA) (uB : 𝟭 B' ⟶ LB) [IsIso uA] [IsIso uB]
    (F : A' ⥤ B') (g : LA ⋙ F ≅ F ⋙ LB)
    (hu : ∀ E, F.map (uA.app E) ≫ g.hom.app E = uB.app (F.obj E)) :
    ∃ (eA : LA ≅ 𝟭 A') (eB : LB ≅ 𝟭 B'),
      (∀ E, uA.app E ≫ eA.hom.app E = 𝟙 E) ∧
      (∀ E, uB.app E ≫ eB.hom.app E = 𝟙 E) ∧
      ∀ E, g.hom.app E ≫ eB.hom.app (F.obj E) = F.map (eA.hom.app E) := by
  let eA := (asIso uA).symm
  let eB := (asIso uB).symm
  have hA (E) : uA.app E ≫ eA.hom.app E = 𝟙 E :=
    (asIso uA).hom_inv_id_app E
  have hB (E) : uB.app E ≫ eB.hom.app E = 𝟙 E :=
    (asIso uB).hom_inv_id_app E
  refine ⟨eA, eB, hA, hB, ?_⟩
  intro E
  apply (cancel_epi (F.map (uA.app E))).mp
  rw [← Category.assoc, hu, hB, ← F.map_comp, hA]
  exact (F.map_id E).symm

private theorem composeProjectionSquare
    {C D : Type*} [Category C] [Category D]
    (F G : C ⥤ D) (p : F ⟶ G) {X Y : C} (f : X ⟶ Y)
    {A B : D} (a : A ⟶ F.obj X) (e : G.obj X ≅ B) (b : A ⟶ B)
    (h : a ≫ p.app X ≫ e.hom = b) :
    a ≫ F.map f ≫ p.app Y = b ≫ e.inv ≫ G.map f := by
  have h' : a ≫ p.app X = b ≫ e.inv :=
    e.eq_comp_inv.mpr ((Category.assoc _ _ _).trans h)
  rw [p.naturality, ← Category.assoc, h', Category.assoc]

private theorem cancelTwoComparisons
    {C : Type*} [Category C] {A B D T : C}
    (a : A ≅ B) (b : D ≅ A) (c d : D ⟶ T) (e : B ⟶ T)
    (h₁ : b.hom ≫ a.hom ≫ e = c) (h₂ : d = c) :
    a.inv ≫ b.inv ≫ d = e := by
  rw [h₂, ← h₁]
  simp only [Iso.inv_hom_id_assoc]

private theorem existsPresentation (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules O)] [HasDerivedCategory.{w} (Towers O)]
    (r : ℕ) (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) :
    ∃ D : RingedKoszulLimitPresentation O r b,
      r = 0 → ∀ E, IsIso (D.unit E) := by
  obtain ⟨D, theta, ht⟩ := exists_ringed_cech_koszul_comparison_on_site O r b
  refine ⟨D, ?_⟩
  intro hr E
  subst r
  have : IsGrothendieckAbelian.{u} (Modules O) := SheafOfModules.isGrothendieckAbelian _
  have : QuasiIso ((CochainComplex.toKInjectiveResolution.{u} (Modules O)).app
      (DerivedCategory.Q.objPreimage E)) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} (Modules O) _).2
  let e := DerivedCategory.Q.objObjPreimageIso E
  have : IsIso (ringedDerivedHomUnit O E) := by
    dsimp only [ringedDerivedHomUnit]
    repeat' apply IsIso.comp_isIso'
    all_goals first | infer_instance | skip
    change IsIso ((derivedInternalHom J O).mapIso ((Iso.refl _).prod e)).hom
    infer_instance
  have : IsIso (ringedCechCompletionUnit O (ringedExtendedCech O 0 b).1
      (ringedExtendedCech O 0 b).2 E) := by
    change IsIso (ringedCechCompletionUnit O (ringedSiteRingComplex O) (𝟙 _) E)
    simp only [ringedCechCompletionUnit, Functor.map_id, op_id]
    change IsIso (ringedDerivedHomUnit O E ≫ (derivedInternalHom J O).map (𝟙 _))
    infer_instance
  rw [← ht E]
  infer_instance

private theorem tensorUnit_naturality (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    {N M : ringedSiteComplex O} (f : N ⟶ M) (m : ℕᵒᵖ) :
    f ≫ ringedKoszulTensorUnitComponent O r b M m =
      ringedKoszulTensorUnitComponent O r b N m ≫
        ((ringedKoszulTensorTower O r b).map f).app m := by
  let : IsGrothendieckAbelian.{u} (Modules O) := SheafOfModules.isGrothendieckAbelian _
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := Classical.choice (SheafOfModules.tensorClosed O).2.1
  have hn := ((ringedKoszulTensor O).map f).naturality (ringedKoszulDualUnit O r b m.unop)
  dsimp only [ringedKoszulTensorUnitComponent, ringedKoszulTensorTower,
    Functor.comp_map, Functor.whiskeringLeft_obj_map, Functor.whiskerLeft_app]
  rw [← Category.assoc]
  have hu : f ≫ (ringedKoszulRightUnitIso O M).inv =
      (ringedKoszulRightUnitIso O N).inv ≫
        ((ringedKoszulTensor O).map f).app (ringedSiteRingComplex O) := by
    exact rightUnitor_inv_naturality f
  rw [hu, Category.assoc, ← hn, ← Category.assoc]

attribute [local irreducible] ringedKoszulTensor ringedKoszulDualTower
  ringedKoszulDiagram SheafOfModules.monoidalCategory coordinate dualCoordinate
  positiveBasis factorBasis degree

private def ordinaryUnitNat (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) :
    𝟭 (ringedSiteComplex O) ⟶ ringedKoszulTensorTowerFunctor O r b ⋙ limitComplex O where
  app N := ringedKoszulLimitUnit O r b N
  naturality {N M} f := by
    apply HomologicalComplex.hom_ext
    intro n
    change f.f n ≫ limit.lift _ (ringedKoszulTensorUnitCone O r b M n) =
      limit.lift _ (ringedKoszulTensorUnitCone O r b N n) ≫
        limMap ((ringedKoszulTensorTowerFunctor O r b).map f |>.f n)
    apply limit.hom_ext
    intro m
    simp only [Category.assoc]
    erw [limit.lift_π, limMap_π]
    rw [← Category.assoc]
    erw [limit.lift_π]
    exact congrArg (fun g ↦ g.f n) (tensorUnit_naturality O r b f m)

private def derivedUnitNat (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules O)] [HasDerivedCategory.{w} (Towers O)]
    {r : ℕ} {b : Fin r → (O.obj ⋙ forget CommRingCat).sections}
    (D : RingedKoszulLimitPresentation O r b) : 𝟭 (ringedSiteDerived O) ⟶ D.completion :=
  let t : DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ D.completion :=
    (DerivedCategory.Q.leftUnitor).inv ≫
    Functor.whiskerRight (ordinaryUnitNat O r b) DerivedCategory.Q ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (ringedKoszulTensorTowerFunctor O r b) D.comparison ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight D.tensorFactors.inv D.inverseLimit ≫
    (Functor.associator _ _ _).hom
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (Modules O) (.up ℤ)) DerivedCategory.Q
    (DerivedCategory.Q ⋙ D.completion) (𝟭 _) D.completion t

private theorem derivedUnitNat_app_Q (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules O)] [HasDerivedCategory.{w} (Towers O)]
    {r : ℕ} {b : Fin r → (O.obj ⋙ forget CommRingCat).sections}
    (D : RingedKoszulLimitPresentation O r b) (N : ringedSiteComplex O) :
    (derivedUnitNat O D).app (DerivedCategory.Q.obj N) = D.unitOnComplex N := by
  simp only [derivedUnitNat, Localization.liftNatTrans_app]
  dsimp [RingedKoszulLimitPresentation.unitOnComplex, ordinaryUnitNat]
  simp only [Category.id_comp, Category.comp_id]
  rfl

private theorem derivedUnitNat_app (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules O)] [HasDerivedCategory.{w} (Towers O)]
    {r : ℕ} {b : Fin r → (O.obj ⋙ forget CommRingCat).sections}
    (D : RingedKoszulLimitPresentation O r b) (E : ringedSiteDerived O) :
    (derivedUnitNat O D).app E = D.unit E := by
  have hn := (derivedUnitNat O D).naturality (DerivedCategory.Q.objObjPreimageIso E).hom
  dsimp only [Functor.id_map] at hn
  rw [derivedUnitNat_app_Q] at hn
  simp only [RingedKoszulLimitPresentation.unit, ← hn, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

private theorem unit_app_Q (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules O)] [HasDerivedCategory.{w} (Towers O)]
    {r : ℕ} {b : Fin r → (O.obj ⋙ forget CommRingCat).sections}
    (D : RingedKoszulLimitPresentation O r b) (N : ringedSiteComplex O) :
    D.unit (DerivedCategory.Q.obj N) = D.unitOnComplex N := by
  rw [← derivedUnitNat_app, derivedUnitNat_app_Q]

private theorem unit_naturality (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules O)] [HasDerivedCategory.{w} (Towers O)]
    {r : ℕ} {b : Fin r → (O.obj ⋙ forget CommRingCat).sections}
    (D : RingedKoszulLimitPresentation O r b)
    {E E' : ringedSiteDerived O} (f : E ⟶ E') :
    f ≫ D.unit E' = D.unit E ≫ D.completion.map f := by
  simpa only [Functor.id_map, derivedUnitNat_app] using (derivedUnitNat O D).naturality f

private theorem unitCompatibility_of_Q (φ : R ⟶ B) (r : ℕ)
    (a : Fin r → (R.obj ⋙ forget CommRingCat).sections)
    (DB : RingedKoszulLimitPresentation B r (imageSections φ a))
    (DR : RingedKoszulLimitPresentation R r a)
    (gamma : DB.completion ⋙ restrictDerived φ ≅ restrictDerived φ ⋙ DR.completion)
    (hq : ∀ N : ringedSiteComplex B,
      (restrictDerived φ).map (DB.unitOnComplex N) ≫
          gamma.hom.app (DerivedCategory.Q.obj N) ≫
          DR.completion.map ((restriction φ).mapDerivedCategoryFactors.hom.app N) =
        (restriction φ).mapDerivedCategoryFactors.hom.app N ≫
          DR.unitOnComplex ((restrictComplex φ).obj N))
    (E : ringedSiteDerived B) :
    (restrictDerived φ).map (DB.unit E) ≫ gamma.hom.app E =
      DR.unit ((restrictDerived φ).obj E) := by
  let t₁ : restrictDerived φ ⟶ restrictDerived φ ⋙ DR.completion :=
    (restrictDerived φ).leftUnitor.inv ≫
      Functor.whiskerRight (derivedUnitNat B DB) (restrictDerived φ) ≫ gamma.hom
  let t₂ : restrictDerived φ ⟶ restrictDerived φ ⋙ DR.completion :=
    (restrictDerived φ).rightUnitor.inv ≫
      Functor.whiskerLeft (restrictDerived φ) (derivedUnitNat R DR)
  have ht : t₁ = t₂ := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (Modules B) (.up ℤ))
    intro N
    dsimp only [t₁, t₂, NatTrans.comp_app, Functor.leftUnitor_inv_app,
      Functor.rightUnitor_inv_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    simp only [Category.id_comp, derivedUnitNat_app]
    apply (cancel_mono (DR.completion.map
      ((restriction φ).mapDerivedCategoryFactors.hom.app N))).mp
    rw [unit_app_Q]
    have hn := unit_naturality R DR ((restriction φ).mapDerivedCategoryFactors.hom.app N)
    erw [← hn, unit_app_Q]
    simpa only [Category.assoc] using hq N
  simpa only [t₁, t₂, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.rightUnitor_inv_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.id_comp, derivedUnitNat_app] using NatTrans.congr_app ht E

private theorem normalizedProjections (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules O)] [HasDerivedCategory.{w} (Towers O)]
    {r : ℕ} {b : Fin r → (O.obj ⋙ forget CommRingCat).sections}
    (D : RingedKoszulLimitPresentation O r b) :
    ∃ p : ∀ m : ℕᵒᵖ, D.inverseLimit ⟶ evaluateDerived O m,
      ∀ (X : CochainComplex (Towers O) ℤ) (m : ℕᵒᵖ),
        D.comparison.app X ≫ (p m).app (DerivedCategory.Q.obj X) ≫
            ((evaluation ℕᵒᵖ (Modules O)).obj m).mapDerivedCategoryFactors.hom.app X =
          DerivedCategory.Q.map ((limitProjection O m).app X) := by
  have := D.isRightDerived
  let W := HomologicalComplex.quasiIso (Towers O) (.up ℤ)
  let β (m : ℕᵒᵖ) : limitComplex O ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ evaluateDerived O m :=
    Functor.whiskerRight (limitProjection O m) DerivedCategory.Q ≫
      ((evaluation ℕᵒᵖ (Modules O)).obj m).mapDerivedCategoryFactors.inv
  let p (m : ℕᵒᵖ) := D.inverseLimit.rightDerivedDesc D.comparison W
    (evaluateDerived O m) (β m)
  refine ⟨p, ?_⟩
  intro X m
  rw [← Category.assoc, Functor.rightDerived_fac_app]
  dsimp only [β, NatTrans.comp_app, Functor.whiskerRight_app]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

private theorem evaluationComparison_normalized (φ : R ⟶ B)
    (X : CochainComplex (Towers B) ℤ) (m : ℕᵒᵖ) :
    (evaluateDerived R m).map ((restrictTower φ).mapDerivedCategoryFactors.inv.app X) ≫
        (evaluationComparison φ m).hom.app (DerivedCategory.Q.obj X) ≫
        (restrictDerived φ).map
          (((evaluation ℕᵒᵖ (Modules B)).obj m).mapDerivedCategoryFactors.hom.app X) =
      ((evaluation ℕᵒᵖ (Modules R)).obj m).mapDerivedCategoryFactors.hom.app
          ((restrictTowerComplex φ).obj X) ≫
        (restriction φ).mapDerivedCategoryFactors.inv.app
          ((((evaluation ℕᵒᵖ (Modules B)).obj m).mapHomologicalComplex (.up ℤ)).obj X) := by
  let Ft := restrictTower φ
  let EB := (evaluation ℕᵒᵖ (Modules B)).obj m
  let ER := (evaluation ℕᵒᵖ (Modules R)).obj m
  let F := restriction φ
  have h₁ := Functor.mapDerivedCategoryCompIso_hom_app_factors Ft ER X
  have h₂ := Functor.mapDerivedCategoryCompIso_hom_app_factors EB F X
  apply (cancel_mono
    (F.mapDerivedCategoryFactors.hom.app ((EB.mapHomologicalComplex (.up ℤ)).obj X))).mp
  dsimp only [evaluationComparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  simp only [Category.assoc]
  change ER.mapDerivedCategory.map (Ft.mapDerivedCategoryFactors.inv.app X) ≫
      (Ft.mapDerivedCategoryCompIso ER).inv.app (DerivedCategory.Q.obj X) ≫
      (EB.mapDerivedCategoryCompIso F).hom.app (DerivedCategory.Q.obj X) ≫
      F.mapDerivedCategory.map (EB.mapDerivedCategoryFactors.hom.app X) ≫
      F.mapDerivedCategoryFactors.hom.app ((EB.mapHomologicalComplex (.up ℤ)).obj X) =
    ER.mapDerivedCategoryFactors.hom.app ((Ft.mapHomologicalComplex (.up ℤ)).obj X) ≫
      F.mapDerivedCategoryFactors.inv.app ((EB.mapHomologicalComplex (.up ℤ)).obj X) ≫
      F.mapDerivedCategoryFactors.hom.app ((EB.mapHomologicalComplex (.up ℤ)).obj X)
  erw [F.mapDerivedCategoryFactors.inv_hom_id_app, Category.comp_id]
  exact cancelTwoComparisons
    (ER.mapDerivedCategory.mapIso (Ft.mapDerivedCategoryFactors.app X))
    ((Ft.mapDerivedCategoryCompIso ER).app (DerivedCategory.Q.obj X))
    ((Ft ⋙ ER).mapDerivedCategoryFactors.hom.app X)
    ((EB.mapDerivedCategoryCompIso F).hom.app (DerivedCategory.Q.obj X) ≫
      F.mapDerivedCategory.map (EB.mapDerivedCategoryFactors.hom.app X) ≫
      F.mapDerivedCategoryFactors.hom.app ((EB.mapHomologicalComplex (.up ℤ)).obj X))
    (ER.mapDerivedCategoryFactors.hom.app ((Ft.mapHomologicalComplex (.up ℤ)).obj X))
    h₁ h₂

omit [HasDerivedCategory.{w} (Modules R)] [HasDerivedCategory.{w} (Modules B)]
  [HasDerivedCategory.{w} (Towers R)] [HasDerivedCategory.{w} (Towers B)] in
private theorem ordinaryUnitRestriction (φ : R ⟶ B) (r : ℕ)
    (a : Fin r → (R.obj ⋙ forget CommRingCat).sections)
    (h : ringedKoszulTensorTowerFunctor B r (imageSections φ a) ⋙
        restrictTowerComplex φ ≅ restrictComplex φ ⋙ ringedKoszulTensorTowerFunctor R r a)
    (hu : ∀ (N : ringedSiteComplex B) (m : ℕᵒᵖ) (n : ℤ),
      (restriction φ).map
          ((ringedKoszulTensorUnitComponent B r (imageSections φ a) N m).f n) ≫
          ((h.hom.app N).f n).app m =
        (ringedKoszulTensorUnitComponent R r a ((restrictComplex φ).obj N) m).f n)
    (N : ringedSiteComplex B) :
    (restrictComplex φ).map (ringedKoszulLimitUnit B r (imageSections φ a) N) ≫
        (limitComparison φ).app ((ringedKoszulTensorTowerFunctor B r
          (imageSections φ a)).obj N) ≫ (limitComplex R).map (h.hom.app N) =
      ringedKoszulLimitUnit R r a ((restrictComplex φ).obj N) := by
  have : PreservesLimitsOfSize.{0, 0} (restriction φ) :=
    preservesSmallestLimits_of_preservesLimits (restriction φ)
  apply HomologicalComplex.hom_ext
  intro n
  apply limit.hom_ext
  intro m
  change ((restriction φ).map (ringedKoszulLimitUnitF B r (imageSections φ a) N n) ≫
      (preservesLimitIso (restriction φ)
        ((ringedKoszulTensorTowerComplex B r (imageSections φ a) N).X n)).hom ≫
      limMap ((h.hom.app N).f n)) ≫ _ =
    ringedKoszulLimitUnitF R r a ((restrictComplex φ).obj N) n ≫ _
  simp only [Category.assoc, limMap_π]
  rw [← Category.assoc _ (limit.π _ m), preservesLimitIso_hom_π]
  simp only [← Functor.map_comp_assoc, ringedKoszulLimitUnitF,
    id_eq, limit.lift_π]
  change (restriction φ).map
      ((ringedKoszulTensorUnitComponent B r (imageSections φ a) N m).f n) ≫
      ((h.hom.app N).f n).app m =
    limit.lift
      ((ringedKoszulTensorTowerComplex R r a ((restrictComplex φ).obj N)).X n)
      (ringedKoszulTensorUnitCone R r a ((restrictComplex φ).obj N) n) ≫
    limit.π
      ((ringedKoszulTensorTowerComplex R r a ((restrictComplex φ).obj N)).X n) m
  rw [limit.lift_π]
  exact hu N m n

omit [HasDerivedCategory.{w} (Modules R)] [HasDerivedCategory.{w} (Modules B)]
  [HasDerivedCategory.{w} (Towers R)] [HasDerivedCategory.{w} (Towers B)] in
private theorem scalarTower_preservesKInjective (φ : R ⟶ B)
    (hflat : PreservesFiniteLimits (SheafOfModules.RingedTensor.tensorFunctor φ) ∧
      PreservesFiniteColimits (SheafOfModules.RingedTensor.tensorFunctor φ)) :
    (restrictTower φ).PreservesKInjectiveComplexes := by
  let E := SheafOfModules.RingedTensor.tensorFunctor φ
  let adj := SheafOfModules.RingedTensor.tensorAdjunction φ
  have : E.Additive := adj.left_adjoint_additive
  have : PreservesFiniteLimits E := hflat.1
  have : PreservesFiniteColimits E := hflat.2
  let ET := (Functor.whiskeringRight ℕᵒᵖ (Modules R) (Modules B)).obj E
  have : PreservesFiniteLimits ET := by
    constructor
    intro T _ _
    exact whiskeringRight_preservesLimitsOfShape _
  have : PreservesFiniteColimits ET := by
    constructor
    intro T _ _
    exact whiskeringRight_preservesColimitsOfShape _
  exact (Adjunction.whiskerRight ℕᵒᵖ adj).preservesKInjectiveComplexes

private theorem normalizedLimitComparison (φ : R ⟶ B)
    (hflat : PreservesFiniteLimits (SheafOfModules.RingedTensor.tensorFunctor φ) ∧
      PreservesFiniteColimits (SheafOfModules.RingedTensor.tensorFunctor φ))
    (r : ℕ) (a : Fin r → (R.obj ⋙ forget CommRingCat).sections)
    (DB : RingedKoszulLimitPresentation B r (imageSections φ a))
    (DR : RingedKoszulLimitPresentation R r a) :
    ∃ alpha : DB.inverseLimit ⋙ restrictDerived φ ≅
        restrictTowerDerived φ ⋙ DR.inverseLimit,
      ∀ X : CochainComplex (Towers B) ℤ,
        (restrictDerived φ).map (DB.comparison.app X) ≫
            alpha.hom.app (DerivedCategory.Q.obj X) =
          (restriction φ).mapDerivedCategoryFactors.hom.app ((limitComplex B).obj X) ≫
            DerivedCategory.Q.map ((limitComparison φ).app X) ≫
            DR.comparison.app ((restrictTowerComplex φ).obj X) ≫
            DR.inverseLimit.map ((restrictTower φ).mapDerivedCategoryFactors.inv.app X) := by
  have : IsGrothendieckAbelian.{u} (Modules B) :=
    SheafOfModules.isGrothendieckAbelian _
  have : IsGrothendieckAbelian.{u} (Towers B) := by
    have := smallModuleDiagrams_isGrothendieckAbelian J
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)
      (ULiftHom.{u} (ULift.{u} ℕᵒᵖ))
    exact IsGrothendieckAbelian.of_equivalence
      (ULiftHomULiftCategory.equiv.{u, u} ℕᵒᵖ).congrLeft.symm
  have : (lim : Towers B ⥤ Modules B).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : (lim : Towers R ⥤ Modules R).Additive :=
    Functor.additive_of_preserves_binary_products _
  have := scalarTower_preservesKInjective φ hflat
  have : PreservesLimitsOfSize.{0, 0} (restriction φ) :=
    preservesSmallestLimits_of_preservesLimits (restriction φ)
  obtain ⟨alpha, ha⟩ := towerComparison_existsLimitIso (restriction φ)
    (restrictDerived φ) (restrictTowerDerived φ) DB.inverseLimit DR.inverseLimit
    (restriction φ).mapDerivedCategoryFactors.inv
    (restrictTower φ).mapDerivedCategoryFactors.inv DB.comparison DR.comparison
    (fun _ _ ↦ inferInstance) (fun _ _ ↦ inferInstance) DB.comparison_isIso
    (fun I hI ↦ by
      have := hI
      exact DR.comparison_isIso _ inferInstance)
    (preservesLimitNatIso (restriction φ) (J := ℕᵒᵖ))
  refine ⟨alpha, ?_⟩
  intro X
  apply (cancel_epi
    ((restriction φ).mapDerivedCategoryFactors.inv.app ((limitComplex B).obj X))).mp
  simpa only [limitComparison, limitComplex, restrictTowerComplex, Category.assoc,
    Iso.inv_hom_id_app_assoc] using ha X

private theorem descendedTensorComparison (φ : R ⟶ B) (r : ℕ)
    (a : Fin r → (R.obj ⋙ forget CommRingCat).sections)
    (DB : RingedKoszulLimitPresentation B r (imageSections φ a))
    (DR : RingedKoszulLimitPresentation R r a)
    (h : ringedKoszulTensorTowerFunctor B r (imageSections φ a) ⋙
        restrictTowerComplex φ ≅ restrictComplex φ ⋙ ringedKoszulTensorTowerFunctor R r a) :
    ∃ hD : DB.tensorTower ⋙ restrictTowerDerived φ ≅ restrictDerived φ ⋙ DR.tensorTower,
      ∀ N : ringedSiteComplex B,
        (restrictTowerDerived φ).map (DB.tensorFactors.hom.app N) ≫
            (restrictTower φ).mapDerivedCategoryFactors.hom.app
              ((ringedKoszulTensorTowerFunctor B r (imageSections φ a)).obj N) ≫
            DerivedCategory.Q.map (h.hom.app N) =
          hD.hom.app (DerivedCategory.Q.obj N) ≫
            DR.tensorTower.map ((restriction φ).mapDerivedCategoryFactors.hom.app N) ≫
            DR.tensorFactors.hom.app ((restrictComplex φ).obj N) := by
  let TB := ringedKoszulTensorTowerFunctor B r (imageSections φ a)
  let TR := ringedKoszulTensorTowerFunctor R r a
  let F := DB.tensorTower ⋙ restrictTowerDerived φ
  let G := restrictDerived φ ⋙ DR.tensorTower
  let e : DerivedCategory.Q ⋙ F ≅ DerivedCategory.Q ⋙ G :=
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight DB.tensorFactors (restrictTowerDerived φ) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft TB (restrictTower φ).mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight h DerivedCategory.Q ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (restrictComplex φ) DR.tensorFactors.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (restriction φ).mapDerivedCategoryFactors.symm DR.tensorTower ≪≫
    Functor.associator _ _ _
  let hD := Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (Modules B) (.up ℤ))
    (DerivedCategory.Q ⋙ F) (DerivedCategory.Q ⋙ G) F G e
  refine ⟨hD, ?_⟩
  intro N
  simp only [hD, Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  dsimp only [Localization.Lifting.iso, Localization.Lifting.compLeft]
  simp only [e, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app, Functor.map_id]
  erw [Category.id_comp, Category.comp_id]

set_option maxHeartbeats 800000 in
-- Normalize the dependent endpoints of the chosen tower and localization functors.
private theorem derivedUnitRestrictionOnComplex (φ : R ⟶ B) (r : ℕ)
    (a : Fin r → (R.obj ⋙ forget CommRingCat).sections)
    (DB : RingedKoszulLimitPresentation B r (imageSections φ a))
    (DR : RingedKoszulLimitPresentation R r a)
    (h : ringedKoszulTensorTowerFunctor B r (imageSections φ a) ⋙
        restrictTowerComplex φ ≅ restrictComplex φ ⋙ ringedKoszulTensorTowerFunctor R r a)
    (hD : DB.tensorTower ⋙ restrictTowerDerived φ ≅ restrictDerived φ ⋙ DR.tensorTower)
    (hd : ∀ N : ringedSiteComplex B,
      (restrictTowerDerived φ).map (DB.tensorFactors.hom.app N) ≫
          (restrictTower φ).mapDerivedCategoryFactors.hom.app
            ((ringedKoszulTensorTowerFunctor B r (imageSections φ a)).obj N) ≫
          DerivedCategory.Q.map (h.hom.app N) =
        hD.hom.app (DerivedCategory.Q.obj N) ≫
          DR.tensorTower.map ((restriction φ).mapDerivedCategoryFactors.hom.app N) ≫
          DR.tensorFactors.hom.app ((restrictComplex φ).obj N))
    (alpha : DB.inverseLimit ⋙ restrictDerived φ ≅
      restrictTowerDerived φ ⋙ DR.inverseLimit)
    (ha : ∀ X : CochainComplex (Towers B) ℤ,
      (restrictDerived φ).map (DB.comparison.app X) ≫
          alpha.hom.app (DerivedCategory.Q.obj X) =
        (restriction φ).mapDerivedCategoryFactors.hom.app ((limitComplex B).obj X) ≫
          DerivedCategory.Q.map ((limitComparison φ).app X) ≫
          DR.comparison.app ((restrictTowerComplex φ).obj X) ≫
          DR.inverseLimit.map ((restrictTower φ).mapDerivedCategoryFactors.inv.app X))
    (hu : ∀ (N : ringedSiteComplex B) (m : ℕᵒᵖ) (n : ℤ),
      (restriction φ).map
          ((ringedKoszulTensorUnitComponent B r (imageSections φ a) N m).f n) ≫
          ((h.hom.app N).f n).app m =
        (ringedKoszulTensorUnitComponent R r a ((restrictComplex φ).obj N) m).f n)
    (N : ringedSiteComplex B) :
    (restrictDerived φ).map (DB.unitOnComplex N) ≫
        alpha.hom.app (DB.tensorTower.obj (DerivedCategory.Q.obj N)) ≫
        DR.inverseLimit.map (hD.hom.app (DerivedCategory.Q.obj N)) ≫
        DR.completion.map ((restriction φ).mapDerivedCategoryFactors.hom.app N) =
      (restriction φ).mapDerivedCategoryFactors.hom.app N ≫
        DR.unitOnComplex ((restrictComplex φ).obj N) := by
  apply (cancel_mono
    (DR.inverseLimit.map (DR.tensorFactors.hom.app ((restrictComplex φ).obj N)))).mp
  have ht := congrArg DR.inverseLimit.map (hd N)
  have hn := alpha.hom.naturality (DB.tensorFactors.hom.app N)
  dsimp only [Functor.comp_map] at hn
  simp only [Functor.map_comp] at ht
  simp only [RingedKoszulLimitPresentation.unitOnComplex,
    Iso.app_inv,
    RingedKoszulLimitPresentation.completion, Functor.comp_map,
    Functor.map_comp, Category.assoc]
  rw [← ht, ← reassoc_of% hn]
  have hbi : (restrictDerived φ).map (DB.inverseLimit.map (DB.tensorFactors.inv.app N)) ≫
      (restrictDerived φ).map (DB.inverseLimit.map (DB.tensorFactors.hom.app N)) = 𝟙 _ := by
    rw [← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id_app,
      Functor.map_id, Functor.map_id]
  have hri : DR.inverseLimit.map (DR.tensorFactors.inv.app ((restrictComplex φ).obj N)) ≫
      DR.inverseLimit.map (DR.tensorFactors.hom.app ((restrictComplex φ).obj N)) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id]
  rw [reassoc_of% hbi, hri]
  erw [reassoc_of% (ha ((ringedKoszulTensorTowerFunctor B r
    (imageSections φ a)).obj N))]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [DR.inverseLimit.map_id, Category.id_comp, Category.comp_id]
  have hv := (restriction φ).mapDerivedCategoryFactors.hom.naturality
    (ringedKoszulLimitUnit B r (imageSections φ a) N)
  dsimp only [Functor.comp_map] at hv
  rw [← Category.assoc]
  erw [hv]
  have hc := DR.comparison.naturality (h.hom.app N)
  dsimp only [Functor.comp_map] at hc
  simp only [Category.assoc]
  erw [← hc]
  simp only [← DerivedCategory.Q.map_comp_assoc]
  erw [ordinaryUnitRestriction φ r a h hu N]
  rfl

set_option maxHeartbeats 800000 in
-- Normalize the dependent endpoints of the chosen tower and localization functors.
private theorem normalizedProjectionSquare (φ : R ⟶ B) (r : ℕ)
    (a : Fin r → (R.obj ⋙ forget CommRingCat).sections)
    (DB : RingedKoszulLimitPresentation B r (imageSections φ a))
    (DR : RingedKoszulLimitPresentation R r a)
    (alpha : DB.inverseLimit ⋙ restrictDerived φ ≅
      restrictTowerDerived φ ⋙ DR.inverseLimit)
    (ha : ∀ X : CochainComplex (Towers B) ℤ,
      (restrictDerived φ).map (DB.comparison.app X) ≫
          alpha.hom.app (DerivedCategory.Q.obj X) =
        (restriction φ).mapDerivedCategoryFactors.hom.app ((limitComplex B).obj X) ≫
          DerivedCategory.Q.map ((limitComparison φ).app X) ≫
          DR.comparison.app ((restrictTowerComplex φ).obj X) ≫
          DR.inverseLimit.map ((restrictTower φ).mapDerivedCategoryFactors.inv.app X))
    (pB : ∀ m : ℕᵒᵖ, DB.inverseLimit ⟶ evaluateDerived B m)
    (pR : ∀ m : ℕᵒᵖ, DR.inverseLimit ⟶ evaluateDerived R m)
    (hpB : ∀ (X : CochainComplex (Towers B) ℤ) (m : ℕᵒᵖ),
      DB.comparison.app X ≫ (pB m).app (DerivedCategory.Q.obj X) ≫
          ((evaluation ℕᵒᵖ (Modules B)).obj m).mapDerivedCategoryFactors.hom.app X =
        DerivedCategory.Q.map ((limitProjection B m).app X))
    (hpR : ∀ (X : CochainComplex (Towers R) ℤ) (m : ℕᵒᵖ),
      DR.comparison.app X ≫ (pR m).app (DerivedCategory.Q.obj X) ≫
          ((evaluation ℕᵒᵖ (Modules R)).obj m).mapDerivedCategoryFactors.hom.app X =
        DerivedCategory.Q.map ((limitProjection R m).app X))
    (M : DerivedCategory (Towers B)) (m : ℕᵒᵖ) :
    alpha.hom.app M ≫ (pR m).app ((restrictTowerDerived φ).obj M) ≫
        (evaluationComparison φ m).hom.app M =
      (restrictDerived φ).map ((pB m).app M) := by
  have : IsGrothendieckAbelian.{u} (Modules B) := SheafOfModules.isGrothendieckAbelian _
  have : IsGrothendieckAbelian.{u} (Towers B) := by
    have := smallModuleDiagrams_isGrothendieckAbelian J
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)
      (ULiftHom.{u} (ULift.{u} ℕᵒᵖ))
    exact IsGrothendieckAbelian.of_equivalence
      (ULiftHomULiftCategory.equiv.{u, u} ℕᵒᵖ).congrLeft.symm
  have : (lim : Towers B ⥤ Modules B).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : PreservesLimitsOfSize.{0, 0} (restriction φ) :=
    preservesSmallestLimits_of_preservesLimits (restriction φ)
  let t₁ : DB.inverseLimit ⋙ restrictDerived φ ⟶
      evaluateDerived B m ⋙ restrictDerived φ :=
    alpha.hom ≫ Functor.whiskerLeft (restrictTowerDerived φ) (pR m) ≫
      (evaluationComparison φ m).hom
  let t₂ : DB.inverseLimit ⋙ restrictDerived φ ⟶
      evaluateDerived B m ⋙ restrictDerived φ :=
    Functor.whiskerRight (pB m) (restrictDerived φ)
  have hI (I : CochainComplex (Towers B) ℤ) (hi : I.IsKInjective) :
      t₁.app (DerivedCategory.Q.obj I) = t₂.app (DerivedCategory.Q.obj I) := by
    have := DB.comparison_isIso I hi
    apply (cancel_epi ((restrictDerived φ).map (DB.comparison.app I))).mp
    change (restrictDerived φ).map (DB.comparison.app I) ≫
        (alpha.hom.app (DerivedCategory.Q.obj I) ≫
          (pR m).app ((restrictTowerDerived φ).obj (DerivedCategory.Q.obj I)) ≫
          (evaluationComparison φ m).hom.app (DerivedCategory.Q.obj I)) =
      (restrictDerived φ).map (DB.comparison.app I) ≫
        (restrictDerived φ).map ((pB m).app (DerivedCategory.Q.obj I))
    apply (cancel_mono ((restrictDerived φ).map
      (((evaluation ℕᵒᵖ (Modules B)).obj m).mapDerivedCategoryFactors.hom.app I))).mp
    have hn := (pR m).naturality ((restrictTower φ).mapDerivedCategoryFactors.inv.app I)
    dsimp only [Functor.comp_map, evaluateDerived] at hn
    have hchain : (limitComparison φ).app I ≫
        (limitProjection R m).app ((restrictTowerComplex φ).obj I) =
      (restrictComplex φ).map ((limitProjection B m).app I) := by
      apply HomologicalComplex.hom_ext
      intro n
      exact preservesLimitIso_hom_π (restriction φ) (I.X n) m
    have hfπ := (restriction φ).mapDerivedCategoryFactors.hom.naturality
      ((limitProjection B m).app I)
    dsimp only [Functor.comp_map] at hfπ
    simp only [Category.assoc]
    rw [reassoc_of% ha, reassoc_of% hn]
    erw [evaluationComparison_normalized φ I m]
    rw [reassoc_of% hpR, ← DerivedCategory.Q.map_comp_assoc, hchain]
    rw [← reassoc_of% hfπ]
    simp only [Iso.hom_inv_id_app]
    rw [← (restrictDerived φ).map_comp, ← (restrictDerived φ).map_comp]
    erw [Category.comp_id]
    exact congrArg (restrictDerived φ).map (hpB I m).symm
  have ht : t₁ = t₂ := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (Towers B) (.up ℤ))
    intro X
    obtain ⟨I, hi, j, _, hj⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective X
    have : IsIso (DerivedCategory.Q.map j) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hj
    apply (cancel_mono ((evaluateDerived B m ⋙ restrictDerived φ).map
      (DerivedCategory.Q.map j))).mp
    rw [← t₁.naturality, ← t₂.naturality, hI I hi]
  exact NatTrans.congr_app ht M

set_option maxHeartbeats 800000 in
-- Assemble the independently normalized comparisons without unfolding their models.
/-- Scalar restriction identifies strict Koszul towers, with the identity on each ordered
exterior coordinate, their coaugmentations, and their normalized total derived limits.
The index m : ℕ represents exponent m+1, hence includes exactly the positive powers.

Source: Stacks Project, algebraization.tex, Tag 0A0E; sites-cohomology.tex, Tags 0A07
and 0941; more-algebra.tex, Tag 0913.
(blueprint: lem-weil-pbc-flat-scalar-koszul-tower-comparison).

Proof:
1. Use the strict ordered-coordinate comparison and its coaugmentation equation.
2. The proved single-site Cech/Koszul comparison supplies both presentations and their
   normalized unit comparisons. Conjugating the localization of the strict comparison
   gives hD with its normalization.
3. Flat extension is an additive exact left adjoint. Its tower adjunction shows that
   restriction preserves K-injective towers. Ordinary restriction preserves limits.
   The generic normalized right-derived limit comparison gives alpha. Right-derived
   descent of each ordinary projection supplies pB and pR.
4. Define gamma as alpha on the tensor tower followed by inverse limit of hD.
   Lift the ordinary Koszul unit to a natural transformation on the derived category;
   its value is the specified representative formula D.unit. The strict unit equation,
   the two normalization equations and comparison naturality give the derived unit
   equation on complexes, hence on the localization.
5. Right-derived uniqueness, evaluated on the ordinary limit projection identity,
   proves the alpha evaluation square. Naturality with hD gives the gamma square.
6. For the empty list use the normalized Cech/Koszul comparison. The Cech
   complex is the ring in degree zero with identity augmentation, so its completion
   unit is the invertible derived Hom-unit. Thus both strict presentation units are
   invertible. Their inverses give eB and eR, and cancellation in the unit equation
   gives the last normalization.
-/
theorem flatScalarKoszulTowerComparison (φ : R ⟶ B)
    (_hflat : PreservesFiniteLimits (SheafOfModules.RingedTensor.tensorFunctor φ) ∧
      PreservesFiniteColimits (SheafOfModules.RingedTensor.tensorFunctor φ))
    (r : ℕ) (a : Fin r → (R.obj ⋙ forget CommRingCat).sections) :
    ∃ (h : ringedKoszulTensorTowerFunctor B r (imageSections φ a) ⋙
          restrictTowerComplex φ ≅
        restrictComplex φ ⋙ ringedKoszulTensorTowerFunctor R r a)
      (DB : RingedKoszulLimitPresentation B r (imageSections φ a))
      (DR : RingedKoszulLimitPresentation R r a)
      (hD : DB.tensorTower ⋙ restrictTowerDerived φ ≅ restrictDerived φ ⋙ DR.tensorTower)
      (alpha : DB.inverseLimit ⋙ restrictDerived φ ≅
        restrictTowerDerived φ ⋙ DR.inverseLimit)
      (gamma : DB.completion ⋙ restrictDerived φ ≅ restrictDerived φ ⋙ DR.completion)
      (pB : ∀ m : ℕᵒᵖ, DB.inverseLimit ⟶ evaluateDerived B m)
      (pR : ∀ m : ℕᵒᵖ, DR.inverseLimit ⟶ evaluateDerived R m),
      (∀ (N : ringedSiteComplex B) (m : ℕ) (e : Fin r → Bool) (n : ℤ),
        ((h.hom.app N).f n).app (op m) ≫
            coordinate R r a ((restrictComplex φ).obj N) m e n =
          (restriction φ).map (coordinate B r (imageSections φ a) N m e n)) ∧
      (∀ (N : ringedSiteComplex B) (m : ℕᵒᵖ) (n : ℤ),
        (restriction φ).map
            ((ringedKoszulTensorUnitComponent B r (imageSections φ a) N m).f n) ≫
            ((h.hom.app N).f n).app m =
          (ringedKoszulTensorUnitComponent R r a ((restrictComplex φ).obj N) m).f n) ∧
      (∀ N : ringedSiteComplex B,
        (restrictTowerDerived φ).map (DB.tensorFactors.hom.app N) ≫
            (restrictTower φ).mapDerivedCategoryFactors.hom.app
              ((ringedKoszulTensorTowerFunctor B r (imageSections φ a)).obj N) ≫
            DerivedCategory.Q.map (h.hom.app N) =
          hD.hom.app (DerivedCategory.Q.obj N) ≫
            DR.tensorTower.map ((restriction φ).mapDerivedCategoryFactors.hom.app N) ≫
            DR.tensorFactors.hom.app ((restrictComplex φ).obj N)) ∧
      (∀ X : CochainComplex (Towers B) ℤ,
        (restrictDerived φ).map (DB.comparison.app X) ≫
            alpha.hom.app (DerivedCategory.Q.obj X) =
          (restriction φ).mapDerivedCategoryFactors.hom.app ((limitComplex B).obj X) ≫
            DerivedCategory.Q.map ((limitComparison φ).app X) ≫
            DR.comparison.app ((restrictTowerComplex φ).obj X) ≫
            DR.inverseLimit.map ((restrictTower φ).mapDerivedCategoryFactors.inv.app X)) ∧
      (∀ E : DerivedCategory (Modules B),
        gamma.hom.app E = alpha.hom.app (DB.tensorTower.obj E) ≫
          DR.inverseLimit.map (hD.hom.app E)) ∧
      (∀ E : DerivedCategory (Modules B),
        (restrictDerived φ).map (DB.unit E) ≫ gamma.hom.app E =
          DR.unit ((restrictDerived φ).obj E)) ∧
      (∀ (X : CochainComplex (Towers B) ℤ) (m : ℕᵒᵖ),
        DB.comparison.app X ≫ (pB m).app (DerivedCategory.Q.obj X) ≫
            ((evaluation ℕᵒᵖ (Modules B)).obj m).mapDerivedCategoryFactors.hom.app X =
          DerivedCategory.Q.map ((limitProjection B m).app X)) ∧
      (∀ (X : CochainComplex (Towers R) ℤ) (m : ℕᵒᵖ),
        DR.comparison.app X ≫ (pR m).app (DerivedCategory.Q.obj X) ≫
            ((evaluation ℕᵒᵖ (Modules R)).obj m).mapDerivedCategoryFactors.hom.app X =
          DerivedCategory.Q.map ((limitProjection R m).app X)) ∧
      (∀ (E : DerivedCategory (Modules B)) (m : ℕᵒᵖ),
        gamma.hom.app E ≫ (pR m).app (DR.tensorTower.obj ((restrictDerived φ).obj E)) =
          (restrictDerived φ).map ((pB m).app (DB.tensorTower.obj E)) ≫
            (evaluationComparison φ m).inv.app (DB.tensorTower.obj E) ≫
            (evaluateDerived R m).map (hD.hom.app E)) ∧
      (r = 0 → ∃ (eB : DB.completion ≅ 𝟭 (DerivedCategory (Modules B)))
          (eR : DR.completion ≅ 𝟭 (DerivedCategory (Modules R))),
        (∀ E, DB.unit E ≫ eB.hom.app E = 𝟙 E) ∧
        (∀ E, DR.unit E ≫ eR.hom.app E = 𝟙 E) ∧
        ∀ E, gamma.hom.app E ≫ eR.hom.app ((restrictDerived φ).obj E) =
          (restrictDerived φ).map (eB.hom.app E)) := by
  obtain ⟨h, hc, hu⟩ := strictScalarKoszulComparison φ r a
  obtain ⟨DB, hB0⟩ := existsPresentation B r (imageSections φ a)
  obtain ⟨DR, hR0⟩ := existsPresentation R r a
  obtain ⟨hD, hd⟩ := descendedTensorComparison φ r a DB DR h
  obtain ⟨alpha, ha⟩ := normalizedLimitComparison φ _hflat r a DB DR
  obtain ⟨pB, hpB⟩ := normalizedProjections B DB
  obtain ⟨pR, hpR⟩ := normalizedProjections R DR
  let gamma : DB.completion ⋙ restrictDerived φ ≅ restrictDerived φ ⋙ DR.completion :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft DB.tensorTower alpha ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight hD DR.inverseLimit ≪≫
      Functor.associator _ _ _
  have hg (E : ringedSiteDerived B) :
      gamma.hom.app E = alpha.hom.app (DB.tensorTower.obj E) ≫
        DR.inverseLimit.map (hD.hom.app E) := by
    simp only [gamma, RingedKoszulLimitPresentation.completion, Functor.comp_obj,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id]
  have hunit (E : ringedSiteDerived B) :
      (restrictDerived φ).map (DB.unit E) ≫ gamma.hom.app E =
        DR.unit ((restrictDerived φ).obj E) := by
    apply unitCompatibility_of_Q φ r a DB DR gamma _ E
    intro N
    rw [hg]
    simpa only [Category.assoc] using
      derivedUnitRestrictionOnComplex φ r a DB DR h hD hd alpha ha hu N
  have hproj (E : ringedSiteDerived B) (m : ℕᵒᵖ) :
      gamma.hom.app E ≫
        (pR m).app (DR.tensorTower.obj ((restrictDerived φ).obj E)) =
      (restrictDerived φ).map ((pB m).app (DB.tensorTower.obj E)) ≫
        (evaluationComparison φ m).inv.app (DB.tensorTower.obj E) ≫
        (evaluateDerived R m).map (hD.hom.app E) := by
    rw [hg, Category.assoc]
    exact composeProjectionSquare DR.inverseLimit (evaluateDerived R m) (pR m)
      (hD.hom.app E) (alpha.hom.app (DB.tensorTower.obj E))
      ((evaluationComparison φ m).app (DB.tensorTower.obj E))
      ((restrictDerived φ).map ((pB m).app (DB.tensorTower.obj E)))
      (normalizedProjectionSquare φ r a DB DR alpha ha pB pR hpB hpR
        (DB.tensorTower.obj E) m)
  refine ⟨h, DB, DR, hD, alpha, gamma, pB, pR,
    hc, hu, hd, ha, hg, hunit, hpB, hpR, hproj, ?_⟩
  intro hr
  have hBI (E : ringedSiteDerived B) : IsIso ((derivedUnitNat B DB).app E) := by
    rw [derivedUnitNat_app]
    exact hB0 hr E
  have hRI (E : ringedSiteDerived R) : IsIso ((derivedUnitNat R DR).app E) := by
    rw [derivedUnitNat_app]
    exact hR0 hr E
  let (E : ringedSiteDerived B) : IsIso ((derivedUnitNat B DB).app E) := hBI E
  let (E : ringedSiteDerived R) : IsIso ((derivedUnitNat R DR).app E) := hRI E
  have : IsIso (derivedUnitNat B DB) := NatIso.isIso_of_isIso_app _
  have : IsIso (derivedUnitNat R DR) := NatIso.isIso_of_isIso_app _
  obtain ⟨eB, eR, hb, hr', he⟩ := inverseUnitComparison
    (derivedUnitNat B DB) (derivedUnitNat R DR) (restrictDerived φ) gamma
    (fun E ↦ by simpa only [derivedUnitNat_app] using hunit E)
  exact ⟨eB, eR, by simpa only [derivedUnitNat_app] using hb,
    by simpa only [derivedUnitNat_app] using hr', he⟩

end CategoryTheory.FlatScalarKoszul
