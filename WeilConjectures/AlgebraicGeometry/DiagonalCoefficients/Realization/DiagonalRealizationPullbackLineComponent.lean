/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Realization.DiagonalRealizationPullbackEndpoints
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Realization.DiagonalRealizationPullbackCanonicalComparison
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Realization.DiagonalRealizationPullbackUnitComponent
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarShift
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.KFlatDerivedAdjunctionTransportShifts
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleDerivedFunctorCompositorShifts

/-! # Canonical derived diagonal realization endpoint comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- A natural transformation commuting with shifts transports a degree-zero endpoint
equation to the corresponding shifted endpoint equation. -/
private theorem shifted_endpoint_square
    {C C' D E : Type*} [Category C] [Category C'] [Category D] [Category E]
    [HasShift C ℤ] [HasShift C' ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (P : C ⥤ C') (FX : C' ⥤ E) (FS : C ⥤ D) (U : D ⥤ E)
    [P.CommShift ℤ] [FX.CommShift ℤ] [FS.CommShift ℤ] [U.CommShift ℤ]
    (Φ : P ⋙ FX ⟶ FS ⋙ U) [NatTrans.CommShift Φ ℤ] (n : ℤ)
    {K : C} {Y : D} {Z : E} {N : C'} (a : FS.obj K ⟶ Y) (b : U.obj Y ⟶ Z)
    (c : P.obj K ⟶ N) (e : FX.obj N ⟶ Z)
    (h : Φ.app K ≫ U.map a ≫ b = FX.map c ≫ e) :
    Φ.app (K⟦n⟧) ≫ U.map ((FS.commShiftIso n).hom.app K ≫ a⟦n⟧') ≫
        ((U.commShiftIso n).hom.app Y ≫ b⟦n⟧') =
      FX.map ((P.commShiftIso n).hom.app K ≫ c⟦n⟧') ≫
        ((FX.commShiftIso n).hom.app N ≫ e⟦n⟧') := by
  have hΦ := NatTrans.shift_app_comm Φ n K
  rw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app] at hΦ
  have hU := (U.commShiftIso n).hom.naturality a
  have hFX := (FX.commShiftIso n).hom.naturality c
  have hh := congrArg (fun k ↦ k⟦n⟧') h
  simp only [Functor.comp_map, Functor.comp_obj, Functor.map_comp, Category.assoc]
    at hΦ hU hFX hh ⊢
  rw [reassoc_of% hU, reassoc_of% hFX, ← reassoc_of% hΦ, hh]

private theorem commShift_ext
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F : C ⥤ D} (s t : F.CommShift ℤ)
    (h : ∀ n, F.commShiftIso (self := s) n = F.commShiftIso (self := t) n) : s = t := by
  cases s
  cases t
  congr 1
  funext n
  exact h n

private theorem adjoint_shift_eq
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    [s : F.CommShift ℤ] [G.CommShift ℤ] [adj.CommShift ℤ] :
    adj.leftAdjointCommShift ℤ = s := by
  apply commShift_ext
  intro n
  exact Adjunction.CommShift.compatibilityUnit_unique_left adj _ _ _
    (Adjunction.LeftAdjointCommShift.compatibilityUnit_iso adj n)
    (adj.shift_unit_app n)

private theorem geometric_shift
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X S : Scheme.{u}} (f : X ⟶ S) :
    NatTrans.CommShift (F₁ := derivedUpper R f)
      (F₂ := (CondensedRing.upperStar R f).mapDerivedCategory)
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R f).hom ℤ := by
  have ha := (CondensedRing.kflat_derived_adjunction_transport_shifts
    (Mon.mk R) f).2.2
  let : (CondensedRing.derivedUpperStarLowerStarAdjunction R f).CommShift ℤ := ha
  have he : derivedUpperCommShift R f =
      CondensedRing.modulePullbackDerivedCommShift R f := by
    exact adjoint_shift_eq
      (F := CondensedRing.moduleObjectDerivedPullback R f)
      (G := CondensedRing.moduleObjectDerivedPushforward R f)
      (CondensedRing.derivedUpperStarLowerStarAdjunction R f)
  change NatTrans.CommShift (F₁ := derivedUpper R f)
    (F₂ := (CondensedRing.upperStar R f).mapDerivedCategory)
    (CondensedRing.modulePullbackExactComparison R f).hom ℤ
  rw [he]
  exact (CondensedRing.module_derived_functors_exact_and_comparison_shifts R f).2.2.1

/-- The canonical derived comparison commutes with the shifts. -/
private theorem derived_comparison_shift
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
    [IsIso (diagonalCompletedCoefficientMap l f)]
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (eX : CompletedRealization l X) (eS : CompletedRealization l S) :
    NatTrans.CommShift (diagonalPullbackDerivedComparison l f eX eS).hom ℤ := by
  let : eS.F.asEquivalence.functor.Additive := inferInstanceAs eS.F.Additive
  let : eX.F.asEquivalence.functor.Additive := inferInstanceAs eX.F.Additive
  let raw := Functor.mapDerivedCategorySquareIso
    (diagonalPullbackOrdinaryComparison l f eX eS)
  let upperIso : derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) f ≅
      (CondensedRing.upperStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).mapDerivedCategory :=
    CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
    (Profinite.continuousMapRingObj.{u} ℤ_[l]) f
  have hg : NatTrans.CommShift
      (F₁ := derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
      (F₂ := (CondensedRing.upperStar
        (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).mapDerivedCategory)
      upperIso.hom ℤ :=
    geometric_shift (Profinite.continuousMapRingObj.{u} ℤ_[l]) f
  have hu : NatTrans.CommShift
      (F₁ := (CondensedRing.upperStar
        (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).mapDerivedCategory)
      (F₂ := derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
      upperIso.symm.hom ℤ := by
    let : NatTrans.CommShift
        (F₁ := derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
        (F₂ := (CondensedRing.upperStar
          (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).mapDerivedCategory)
        upperIso.hom ℤ := hg
    infer_instance
  have hr : NatTrans.CommShift raw.hom ℤ := by
    dsimp [raw]
    infer_instance
  let : NatTrans.CommShift
      (F₁ := (CondensedRing.upperStar
        (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).mapDerivedCategory)
      (F₂ := derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
      upperIso.symm.hom ℤ := hu
  have hc : NatTrans.CommShift
      (F₁ := (Scheme.proEtaleRingModulePullback f
        (Scheme.purTwistZlCompletion S l) (Scheme.purTwistZlCompletion X l)
        (diagonalPullbackCoefficientIso l f)).mapDerivedCategory ⋙ eX.F.mapDerivedCategory)
      (F₂ := eS.F.mapDerivedCategory ⋙
        derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
      (raw.hom ≫ Functor.whiskerLeft eS.F.mapDerivedCategory upperIso.symm.hom) ℤ := by
    exact NatTrans.CommShift.comp (τ := raw.hom)
      (τ' := Functor.whiskerLeft eS.F.mapDerivedCategory upperIso.symm.hom) ℤ
  simpa only [diagonalPullbackDerivedComparison, raw,
    derivedUpper, upperIso, Iso.trans_hom, Functor.isoWhiskerLeft_hom] using hc

open MonObj in
/-- The unit of the free-module adjunction inserts the unit of the ring. -/
private theorem freeForgetAdjunction_unit_app {C : Type*} [Category C] [MonoidalCategory C]
    (R : C) [MonObj R] (M : C) :
    (Mod.freeForgetAdjunction R).unit.app M = (λ_ M).inv ≫ η[R] ▷ M := by
  simp only [Mod.freeForgetAdjunction, Adjunction.mkOfHomEquiv_unit_app]
  exact congrArg _ (Category.comp_id _)

open MonObj in
/-- Pulling back the insertion of the unit and then applying a ring map and a module map
is the insertion of the unit of the target. -/
private theorem unitInsertion_map_δ {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] {R : C} [MonObj R] {R' : D} [MonObj R']
    (a : F.obj R ⟶ R') [IsMonHom a] {M : C} {N : D} (g : F.obj M ⟶ N) :
    F.map ((λ_ M).inv ≫ η[R] ▷ M) ≫ Functor.OplaxMonoidal.δ F R M ≫ (a ⊗ₘ g) =
      g ≫ (λ_ N).inv ≫ η[R'] ▷ N := by
  have h1 : (Functor.LaxMonoidal.ε F ≫ F.map η[R]) ≫ a = η[R'] :=
    IsMonHom.one_hom (f := a)
  rw [Functor.map_comp, Category.assoc, ← Functor.OplaxMonoidal.δ_natural_left_assoc,
    ← Functor.LaxMonoidal.left_unitality_inv, Category.assoc, Category.assoc,
    Functor.Monoidal.μ_δ_assoc, MonoidalCategory.tensorHom_def,
    ← MonoidalCategory.comp_whiskerRight_assoc, ← MonoidalCategory.comp_whiskerRight_assoc, h1,
    ← MonoidalCategory.whisker_exchange, MonoidalCategory.leftUnitor_inv_naturality_assoc]

/-- Pulling back a free-module unit and then applying a ring map and a module map is the
free-module unit of the target. -/
private theorem freeUnit_map_δ {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] {R : C} [MonObj R] {R' : D} [MonObj R']
    (a : F.obj R ⟶ R') [IsMonHom a] {M : C} {N : D} (g : F.obj M ⟶ N) :
    F.map ((Mod.freeForgetAdjunction R).unit.app M) ≫ Functor.OplaxMonoidal.δ F R M ≫
        (a ⊗ₘ g) = g ≫ (Mod.freeForgetAdjunction R').unit.app N := by
  rw [freeForgetAdjunction_unit_app, freeForgetAdjunction_unit_app]
  exact unitInsertion_map_δ F a g
/-- A map into a direct image which is compatible with the root projections and the free
units agrees with the adjunct of a comparison specified by the same projections. -/
private theorem root_projection_square
    {C D : Type*} [Category C] [Category D] {Fu : C ⥤ D} {G : D ⥤ C} (adj : Fu ⊣ G)
    {PS LS TS μS : C} {PX LX TX μX : D}
    (mS : PS ⟶ G.obj PX) (rX : PX ⟶ LX) (πX : LX ⟶ TX) (rS : PS ⟶ LS) (πS : LS ⟶ TS)
    (c : Fu.obj LS ⟶ LX) (qX : PX ⟶ μX) (uX : μX ⟶ TX) (qS : PS ⟶ μS) (uS : μS ⟶ TS)
    (k : Fu.obj TS ⟶ TX) (i : Fu.obj μS ⟶ μX)
    (hrX : rX ≫ πX = qX ≫ uX) (hrS : rS ≫ πS = qS ≫ uS)
    (hc : c ≫ πX = Fu.map πS ≫ k) (hb : Fu.map uS ≫ k = i ≫ uX)
    (ha : mS ≫ G.map qX = qS ≫ adj.homEquiv _ _ i) :
    (mS ≫ G.map rX) ≫ G.map πX = (rS ≫ adj.homEquiv _ _ c) ≫ G.map πX := by
  rw [Category.assoc, Category.assoc, ← G.map_comp, hrX, G.map_comp, reassoc_of% ha,
    ← adj.homEquiv_naturality_right, ← adj.homEquiv_naturality_right, hc,
    adj.homEquiv_naturality_left, reassoc_of% hrS, ← hb, adj.homEquiv_naturality_left]

/-- Assemble an underlying endpoint square from a source naturality square, a target
normalization square and a core square. -/
private theorem endpoint_underlying_square
    {C D : Type*} [Category C] [Category D] (G : D ⥤ C)
    {A B A' T : C} {X₁ X₂ X₃ : D}
    (a : A ⟶ B) (b : B ⟶ G.obj X₁) (x : X₁ ⟶ X₂) (r : X₂ ⟶ X₃)
    (uS : A ⟶ A') (mS : A' ⟶ G.obj X₂) (uP : B ⟶ G.obj X₂) (rS : A' ⟶ T)
    (h : T ⟶ G.obj X₃)
    (ho : b ≫ G.map x = uP) (hn : a ≫ uP = uS ≫ mS)
    (hcore : mS ≫ G.map r = rS ≫ h) :
    a ≫ b ≫ G.map (x ≫ r) = (uS ≫ rS) ≫ h := by
  rw [G.map_comp, reassoc_of% ho, reassoc_of% hn, hcore, Category.assoc]

/-- The underlying map of the adjunct of the completed line endpoint, followed by the
direct image of the root map, is the root map followed by the adjunct of the integral
comparison. -/
private theorem line_adjunct_roots
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
    [IsIso (diagonalCompletedCoefficientMap l f)]
    (rX : IntegralRoots l (bottomField l) X) (rS : IntegralRoots l (bottomField l) S)
    (d : DiagonalRealizationPullbackEndpointData l f (diagonalPullbackCoefficientIso l f)) :
    (diagonalCompletedRestriction l S ⋙ diagonalForget l S).map
        ((Scheme.proEtaleRingModuleAdjunction f (Scheme.purTwistZlCompletion S l)
          (Scheme.purTwistZlCompletion X l) (diagonalPullbackCoefficientIso l f)).homEquiv _ _
            d.completedLine.hom ≫ (diagonalPullbackPushBridge l f).inv.app _) ≫
        (lowerStar Ab.{u + 1} f).map rX.hom =
      rS.hom ≫ (Scheme.proEtaleSheafAdjunction f Ab.{u + 1}).homEquiv _ _
        (spIntegralComparison f l (bottomField l)) := by
  let UX := Mod.forget (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.padicIntegersRingObj.{u} l (bottomField l).1) X)
  apply (isLimitOfPreserves (lowerStar Ab.{u + 1} f) (isLimitOfPreserves UX
    (limit.isLimit (spIntegralTwistSystem X l (bottomField l))))).hom_ext
  rintro ⟨n⟩
  have hrX := rX.projections n
  have hrS := rS.projections n
  have hspec := (Classical.choose_spec
    (spIntegralComparison_existsUnique f l (bottomField l))).1 n
  have ha : (diagonalCompletedRestriction l S ⋙ diagonalForget l S).map
        ((Scheme.proEtaleRingModuleAdjunction f (Scheme.purTwistZlCompletion S l)
          (Scheme.purTwistZlCompletion X l) (diagonalPullbackCoefficientIso l f)).homEquiv _ _
            d.completedLine.hom ≫ (diagonalPullbackPushBridge l f).inv.app _) ≫
        (lowerStar Ab.{u + 1} f).map
          (limit.π (Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)) (op n)) =
      limit.π (Scheme.proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)) (op n) ≫
        (Scheme.proEtaleSheafAdjunction f Ab.{u + 1}).homEquiv _ _
          (Scheme.proEtaleRootsOfUnityInverseImageMap f (l ^ (n + 1))) := by
    rw [Scheme.proEtaleRootsOfUnityInverseImageMap]
    erw [Equiv.apply_symm_apply]
    ext U z
    have h := d.completedLine_normalization n U z
    exact h
  have hb := freeUnit_map_δ (upperStar AddCommGrpCat.{u + 1} f)
    (condensedPullbackHom (spEllPointRingObj.{u} l (bottomField l) n) f)
    (Scheme.proEtaleRootsOfUnityInverseImageMap f (l ^ (n + 1)))
  exact root_projection_square (Scheme.proEtaleSheafAdjunction f Ab.{u + 1})
    ((diagonalCompletedRestriction l S ⋙ diagonalForget l S).map
        ((Scheme.proEtaleRingModuleAdjunction f (Scheme.purTwistZlCompletion S l)
          (Scheme.purTwistZlCompletion X l) (diagonalPullbackCoefficientIso l f)).homEquiv _ _
            d.completedLine.hom ≫ (diagonalPullbackPushBridge l f).inv.app _))
    rX.hom (limit.π (spIntegralTwistSystem X l (bottomField l)) (op n)).hom
    rS.hom (limit.π (spIntegralTwistSystem S l (bottomField l)) (op n)).hom
    (spIntegralComparison f l (bottomField l))
    (limit.π (Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)) (op n))
    ((Mod.freeForgetAdjunction
      (condensedRingObj (spEllPointRingObj l (bottomField l) n) X)).unit.app
      (Scheme.proEtaleRootsOfUnitySheaf X (l ^ (n + 1))))
    (limit.π (Scheme.proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)) (op n))
    ((Mod.freeForgetAdjunction
      (condensedRingObj (spEllPointRingObj l (bottomField l) n) S)).unit.app
      (Scheme.proEtaleRootsOfUnitySheaf S (l ^ (n + 1))))
    _ (Scheme.proEtaleRootsOfUnityInverseImageMap f (l ^ (n + 1))) hrX hrS hspec hb ha

/-- The source equation for the line: the realized adjunct of the completed line
endpoint is the realized adjunct of the condensed line endpoint. -/
private theorem source_line_equation
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
    [IsIso (diagonalCompletedCoefficientMap l f)]
    (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    (square : CompletedOrdinarySquare l f eX eS)
    (line : PullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) f
      (zlLine l S) (zlLine l X)
      (((upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _).symm
        ((Scheme.proEtaleSheafAdjunction f Ab.{u + 1}).homEquiv _ _
          (spIntegralComparison f l (bottomField l)))))
    (d : DiagonalRealizationPullbackEndpointData l f (diagonalPullbackCoefficientIso l f)) :
    eS.F.map ((Scheme.proEtaleRingModuleAdjunction f (Scheme.purTwistZlCompletion S l)
        (Scheme.purTwistZlCompletion X l) (diagonalPullbackCoefficientIso l f)).homEquiv _ _
          d.completedLine.hom ≫ (diagonalPullbackPushBridge l f).inv.app _) ≫
        square.ordinary.hom.app _ ≫
        (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).map
          eX.lineIso.hom =
      eS.lineIso.hom ≫
        (CondensedRing.upperStarLowerStarAdjunction
          (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).homEquiv _ _ line.iso.hom := by
  have ho := eq_of_heq (square.normalization (Scheme.purTwistZlModule X l))
  have hn := eS.underlying.hom.naturality
    ((Scheme.proEtaleRingModuleAdjunction f (Scheme.purTwistZlCompletion S l)
      (Scheme.purTwistZlCompletion X l) (diagonalPullbackCoefficientIso l f)).homEquiv _ _
        d.completedLine.hom ≫ (diagonalPullbackPushBridge l f).inv.app _)
  have hlX := eq_of_heq eX.line_normalization
  have hlS := eq_of_heq eS.line_normalization
  have hline := line.normalization
  rw [Equiv.apply_symm_apply] at hline
  apply Mod.hom_ext
  simp only [Mod.comp_hom', CondensedRing.lowerStar_map_hom]
  have hX' : eX.lineIso.hom.hom = eX.underlying.hom.app _ ≫ eX.roots.hom := by
    rw [← hlX]
    erw [Iso.hom_inv_id_app_assoc]
  have hS' : eS.lineIso.hom.hom = eS.underlying.hom.app _ ≫ eS.roots.hom := by
    rw [← hlS]
    erw [Iso.hom_inv_id_app_assoc]
  rw [hline, hX', hS']
  exact endpoint_underlying_square _ _ _ _ _ _ _ _ _ _ ho hn
    (line_adjunct_roots l f eX.roots eS.roots d)

private theorem ordinary_line_component
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
    [IsIso (diagonalCompletedCoefficientMap l f)]
    (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    (line : PullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) f
      (zlLine l S) (zlLine l X)
      (((upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _).symm
        ((Scheme.proEtaleSheafAdjunction f Ab.{u + 1}).homEquiv _ _
          (spIntegralComparison f l (bottomField l)))))
    (d : DiagonalRealizationPullbackEndpointData l f (diagonalPullbackCoefficientIso l f)) :
    (diagonalPullbackOrdinaryComparison l f eX eS).hom.app (Scheme.purTwistZlModule S l) ≫
      (CondensedRing.upperStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).map
        eS.lineIso.hom ≫ line.iso.hom =
    eX.F.map d.completedLine.hom ≫ eX.lineIso.hom := by
  exact ordinary_bridge_endpoint
    (Scheme.proEtaleRingModuleAdjunction f (Scheme.purTwistZlCompletion S l)
      (Scheme.purTwistZlCompletion X l) (diagonalPullbackCoefficientIso l f))
    (CondensedRing.upperStarLowerStarAdjunction
      (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    eS.F eX.F (diagonalTracePush l f) (diagonalPullbackPushBridge l f)
    (Classical.choice (completedCoefficientOrdinarySquare_exists l f eX eS)).ordinary
    (diagonalPullbackOrdinaryComparison l f eX eS)
    (diagonalPullbackRightComparison l f eX eS)
    (diagonalPullbackOrdinaryComparison_transpose l f eX eS)
    (right_comparison_eq l f eX eS)
    (Scheme.purTwistZlModule S l) (Scheme.purTwistZlModule X l)
    _ _ d.completedLine eS.lineIso eX.lineIso line.iso
    ((Scheme.proEtaleRingModuleAdjunction f (Scheme.purTwistZlCompletion S l)
        (Scheme.purTwistZlCompletion X l) (diagonalPullbackCoefficientIso l f)).homEquiv _ _
          d.completedLine.hom ≫ (diagonalPullbackPushBridge l f).inv.app _)
    line.iso.hom
    (by rw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]) rfl
    (source_line_equation l f eX eS
      (Classical.choice (completedCoefficientOrdinarySquare_exists l f eX eS)) line d)

private theorem canonical_derived_line
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
    [IsIso (diagonalCompletedCoefficientMap l f)]
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    (line : PullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) f
      (zlLine l S) (zlLine l X)
      (((upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _).symm
        ((Scheme.proEtaleSheafAdjunction f Ab.{u + 1}).homEquiv _ _
          (spIntegralComparison f l (bottomField l)))))
    (d : DiagonalRealizationPullbackEndpointData l f (diagonalPullbackCoefficientIso l f)) :
    (diagonalPullbackDerivedComparison l f eX eS).hom.app
        (DiagonalTrace.completedLine l S) ≫
      (derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).map
        ((eS.F.mapDerivedCategorySingleFunctor 0).hom.app (Scheme.purTwistZlModule S l) ≫
          (DerivedCategory.singleFunctor
            (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) S) 0).map eS.lineIso.hom) ≫
        line.derived =
    eX.F.mapDerivedCategory.map
      ((Scheme.proEtaleRingModulePullback f
          (Scheme.purTwistZlCompletion S l) (Scheme.purTwistZlCompletion X l)
          (diagonalPullbackCoefficientIso l f)).mapDerivedCategorySingleFunctor 0 |>.app
          (Scheme.purTwistZlModule S l)
        |>.trans ((DerivedCategory.singleFunctor (DiagonalCompleted l X) 0).mapIso
          d.completedLine)).hom ≫
      ((eX.F.mapDerivedCategorySingleFunctor 0).hom.app (Scheme.purTwistZlModule X l) ≫
        (DerivedCategory.singleFunctor
          (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) X) 0).map eX.lineIso.hom) := by
  rw [derived_comparison_eq]
  simp only [PullEndpoint.derived, single_pullback_eq, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom]
  exact derived_endpoint_square
    (Scheme.proEtaleRingModulePullback f (Scheme.purTwistZlCompletion S l)
      (Scheme.purTwistZlCompletion X l) (diagonalPullbackCoefficientIso l f))
    eX.F eS.F (CondensedRing.upperStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (diagonalPullbackOrdinaryComparison l f eX eS)
    (Scheme.purTwistZlModule S l)
    d.completedLine eS.lineIso eX.lineIso line.iso
    (derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
      (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (ordinary_line_component l f eX eS line d)

/-- The canonical derived comparison has the prescribed shifted-line component. -/
theorem diagonalRealization_pullback_line_component
    (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian X] [IsNoetherian S]
    (coeff : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (Scheme.purTwistZlCompletion S l) ≅ Scheme.purTwistZlCompletion X l)
    (hc : coeff.hom = diagonalCompletedCoefficientMap l f)
    (_hX : IsUnit (l : Γ(X, ⊤))) (_hS : IsUnit (l : Γ(S, ⊤)))
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    (_unit : UnitPullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (line : PullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) f
      (zlLine l S) (zlLine l X)
      (((upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _).symm
        ((Scheme.proEtaleSheafAdjunction f Ab.{u + 1}).homEquiv _ _
          (spIntegralComparison f l (bottomField l)))))
    (d : DiagonalRealizationPullbackEndpointData l f coeff) :
    (diagonalRealization_pullback_canonical_comparison l f eX eS coeff hc).hom.app
      ((DiagonalTrace.completedLine l S)⟦(2 : ℤ)⟧) ≫
      (derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).map
        (eS.shiftedLine l S) ≫ line.shift =
    eX.F.mapDerivedCategory.map
      (((Scheme.proEtaleRingModulePullback f (Scheme.purTwistZlCompletion S l)
        (Scheme.purTwistZlCompletion X l) coeff).mapDerivedCategory.commShiftIso (2 : ℤ)).app _
      ≪≫ (shiftFunctor (DerivedCategory (DiagonalCompleted l X)) (2 : ℤ)).mapIso
        ((Scheme.proEtaleRingModulePullback f (Scheme.purTwistZlCompletion S l)
          (Scheme.purTwistZlCompletion X l) coeff).mapDerivedCategorySingleFunctor 0 |>.app
            (Scheme.purTwistZlModule S l) |>.trans
              ((DerivedCategory.singleFunctor (DiagonalCompleted l X) 0).mapIso
                d.completedLine))).hom ≫
      eX.shiftedLine l X := by
  have hmap : IsIso (diagonalCompletedCoefficientMap l f) := by
    rw [← hc]
    infer_instance
  have hcoeff : coeff = diagonalPullbackCoefficientIso l f := Iso.ext hc
  subst coeff
  rw [diagonalRealization_pullback_canonical_comparison_normalized]
  have := derived_comparison_shift l f eX eS
  simp only [CompletedRealization.shiftedLine, PullEndpoint.shift, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom]
  rw [← Functor.map_comp, ← Functor.map_comp]
  have key := shifted_endpoint_square
    (Scheme.proEtaleRingModulePullback f (Scheme.purTwistZlCompletion S l)
      (Scheme.purTwistZlCompletion X l) (diagonalPullbackCoefficientIso l f)).mapDerivedCategory
    eX.F.mapDerivedCategory eS.F.mapDerivedCategory
    (derivedUpper (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (diagonalPullbackDerivedComparison l f eX eS).hom 2
    ((eS.F.mapDerivedCategorySingleFunctor 0).hom.app (Scheme.purTwistZlModule S l) ≫
      (DerivedCategory.singleFunctor
        (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) S) 0).map eS.lineIso.hom)
    line.derived
    ((Scheme.proEtaleRingModulePullback f
        (Scheme.purTwistZlCompletion S l) (Scheme.purTwistZlCompletion X l)
        (diagonalPullbackCoefficientIso l f)).mapDerivedCategorySingleFunctor 0 |>.app
        (Scheme.purTwistZlModule S l)
      |>.trans ((DerivedCategory.singleFunctor (DiagonalCompleted l X) 0).mapIso
        d.completedLine)).hom
    ((eX.F.mapDerivedCategorySingleFunctor 0).hom.app (Scheme.purTwistZlModule X l) ≫
      (DerivedCategory.singleFunctor
        (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) X) 0).map eX.lineIso.hom)
    (canonical_derived_line l f eX eS line d)
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] at key
  convert key using 2

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
