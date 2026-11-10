/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.FiniteOpenBaseChangeNormalized
public import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionSquare
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
public import WeilConjectures.AlgebraicGeometry.Stratum.StratumScalarExtension
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryRestrictionPullbackSquare

/-! Normalization data for the scalar/open exchange argument. -/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

local notation "CR" => Scheme.proEtaleConstantRing
local notation "PB" => Scheme.proEtaleConstantRingDerivedPullback
local notation "AD" => Scheme.proEtaleRingDerivedOpenAdjunction
local notation "CC" => Scheme.proEtaleConstantRingComparison
local notation "OE" => Scheme.proEtaleRingDerivedOpenExtension

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem mateCube
    {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃]
    {S₀ : C₀ ⥤ D₀} {R₀ : D₀ ⥤ C₀} {S₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁}
    {S₂ : C₂ ⥤ D₂} {R₂ : D₂ ⥤ C₂} {S₃ : C₃ ⥤ D₃} {R₃ : D₃ ⥤ C₃}
    (a₀ : S₀ ⊣ R₀) (a₁ : S₁ ⊣ R₁) (a₂ : S₂ ⊣ R₂) (a₃ : S₃ ⊣ R₃)
    {J : C₀ ⥤ C₁} {H : C₁ ⥤ C₃} {G : C₀ ⥤ C₂} {I : C₂ ⥤ C₃}
    {J' : D₀ ⥤ D₁} {H' : D₁ ⥤ D₃} {G' : D₀ ⥤ D₂} {I' : D₂ ⥤ D₃}
    (qJ : R₀ ⋙ J ⟶ J' ⋙ R₁) (qH : R₁ ⋙ H ⟶ H' ⋙ R₃)
    (qG : R₀ ⋙ G ⟶ G' ⋙ R₂) (qI : R₂ ⋙ I ⟶ I' ⋙ R₃)
    (c : J ⋙ H ⟶ G ⋙ I) (d : J' ⋙ H' ⟶ G' ⋙ I')
    (hc : ∀ M, c.app (R₀.obj M) ≫ I.map (qG.app M) ≫ qI.app (G'.obj M) =
      H.map (qJ.app M) ≫ qH.app (J'.obj M) ≫ R₃.map (d.app M))
    (N : C₀) :
    S₃.map (c.app N) ≫
        ((mateEquiv a₂ a₃).symm (TwoSquare.mk _ _ _ _ qI)).app (G.obj N) ≫
        I'.map (((mateEquiv a₀ a₂).symm (TwoSquare.mk _ _ _ _ qG)).app N) =
      ((mateEquiv a₁ a₃).symm (TwoSquare.mk _ _ _ _ qH)).app (J.obj N) ≫
        H'.map (((mateEquiv a₀ a₁).symm (TwoSquare.mk _ _ _ _ qJ)).app N) ≫
        d.app (S₀.obj N) := by
  let lJ := ((mateEquiv a₀ a₁).symm (TwoSquare.mk _ _ _ _ qJ)).natTrans
  let lH := ((mateEquiv a₁ a₃).symm (TwoSquare.mk _ _ _ _ qH)).natTrans
  let lG := ((mateEquiv a₀ a₂).symm (TwoSquare.mk _ _ _ _ qG)).natTrans
  let lI := ((mateEquiv a₂ a₃).symm (TwoSquare.mk _ _ _ _ qI)).natTrans
  have hj (K : C₀) : J.map (a₀.unit.app K) ≫ qJ.app (S₀.obj K) =
      a₁.unit.app (J.obj K) ≫ R₁.map (lJ.app K) :=
    unit_mateEquiv_symm a₀ a₁ (TwoSquare.mk _ _ _ _ qJ) K
  have hh (K : C₁) : H.map (a₁.unit.app K) ≫ qH.app (S₁.obj K) =
      a₃.unit.app (H.obj K) ≫ R₃.map (lH.app K) :=
    unit_mateEquiv_symm a₁ a₃ (TwoSquare.mk _ _ _ _ qH) K
  have hg (K : C₀) : G.map (a₀.unit.app K) ≫ qG.app (S₀.obj K) =
      a₂.unit.app (G.obj K) ≫ R₂.map (lG.app K) :=
    unit_mateEquiv_symm a₀ a₂ (TwoSquare.mk _ _ _ _ qG) K
  have hi (K : C₂) : I.map (a₂.unit.app K) ≫ qI.app (S₂.obj K) =
      a₃.unit.app (I.obj K) ≫ R₃.map (lI.app K) :=
    unit_mateEquiv_symm a₂ a₃ (TwoSquare.mk _ _ _ _ qI) K
  change S₃.map (c.app N) ≫ lI.app (G.obj N) ≫ I'.map (lG.app N) =
    lH.app (J.obj N) ≫ H'.map (lJ.app N) ≫ d.app (S₀.obj N)
  apply (a₃.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Functor.comp_obj]
  have hn := a₃.unit.naturality (c.app N)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at hn
  rw [← reassoc_of% hn, ← reassoc_of% (hi (G.obj N))]
  have hq := qI.naturality (lG.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hq
  rw [← hq, ← I.map_comp_assoc, ← hg, I.map_comp]
  have hcn := c.naturality (a₀.unit.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hcn
  simp only [Category.assoc, Functor.id_obj] at hcn ⊢
  rw [← reassoc_of% hcn, hc]
  rw [← reassoc_of% (hh (J.obj N))]
  have hqn := qH.naturality (lJ.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hqn
  rw [← reassoc_of% hqn, ← H.map_comp_assoc, hj]
  simp only [Functor.map_comp, Category.assoc]

private noncomputable abbrev tripleComparison :
    (L ⋙ M ⋙ N).mapDerivedCategory ≅
      L.mapDerivedCategory ⋙ M.mapDerivedCategory ⋙ N.mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso (L ⋙ M) N ≪≫
    isoWhiskerRight (Functor.mapDerivedCategoryCompIso L M) N.mapDerivedCategory

private lemma tripleComparison_hom :
    (tripleComparison L M N).hom =
      (Functor.mapDerivedCategoryCompIso L (M ⋙ N)).hom ≫
        Functor.whiskerLeft L.mapDerivedCategory (Functor.mapDerivedCategoryCompIso M N).hom :=
  (Functor.mapDerivedCategoryCompIso_assoc L M N).symm

private lemma tripleComparison_right (e : L ⋙ M ≅ L' ⋙ M') :
    (tripleComparison L M N).hom ≫
        Functor.whiskerRight (Functor.mapDerivedCategorySquareIso e).hom
          N.mapDerivedCategory =
      (Functor.mapDerivedCategoryNatIso (isoWhiskerRight e N)).hom ≫
        (tripleComparison L' M' N).hom := by
  dsimp only [tripleComparison, Functor.mapDerivedCategorySquareIso]
  simp only [Iso.trans_hom, Iso.symm_hom,
    isoWhiskerRight_hom, Functor.whiskerRight_comp, Category.assoc]
  rw [← reassoc_of% (Functor.whiskerRight_comp
    (Functor.mapDerivedCategoryCompIso L M).hom
    (Functor.mapDerivedCategoryCompIso L M).inv N.mapDerivedCategory), Iso.hom_inv_id]
  simp only [Functor.whiskerRight_id', Category.id_comp]
  rw [← reassoc_of% (Functor.mapDerivedCategoryNatIso_isoWhiskerRight e N)]

private lemma tripleComparison_left (e : M ⋙ N ≅ M'' ⋙ N') :
    (tripleComparison L M N).hom ≫
        Functor.whiskerLeft L.mapDerivedCategory
          (Functor.mapDerivedCategorySquareIso e).hom =
      (Functor.mapDerivedCategoryNatIso (isoWhiskerLeft L e)).hom ≫
        (tripleComparison L M'' N').hom := by
  rw [tripleComparison_hom, tripleComparison_hom]
  dsimp only [Functor.mapDerivedCategorySquareIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.whiskerLeft_comp, Category.assoc]
  rw [← reassoc_of% (Functor.whiskerLeft_comp L.mapDerivedCategory
    (Functor.mapDerivedCategoryCompIso M N).hom
    (Functor.mapDerivedCategoryCompIso M N).inv), Iso.hom_inv_id]
  simp only [Functor.whiskerLeft_id', Category.id_comp]
  rw [← reassoc_of% (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft L e)]

private lemma derivedCube
    (qJ : R₀ ⋙ J ≅ J' ⋙ R₁) (qH : R₁ ⋙ H ≅ H' ⋙ R₃)
    (qG : R₀ ⋙ G ≅ G' ⋙ R₂) (qI : R₂ ⋙ I ≅ I' ⋙ R₃)
    (c : J ⋙ H ≅ G ⋙ I) (d : J' ⋙ H' ≅ G' ⋙ I')
    (hc : ∀ M, c.hom.app (R₀.obj M) ≫ I.map (qG.hom.app M) ≫ qI.hom.app (G'.obj M) =
      H.map (qJ.hom.app M) ≫ qH.hom.app (J'.obj M) ≫ R₃.map (d.hom.app M))
    (M : DerivedCategory D₀) :
    (Functor.mapDerivedCategorySquareIso c).hom.app (R₀.mapDerivedCategory.obj M) ≫
        I.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso qG).hom.app M) ≫
        (Functor.mapDerivedCategorySquareIso qI).hom.app (G'.mapDerivedCategory.obj M) =
      H.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso qJ).hom.app M) ≫
        (Functor.mapDerivedCategorySquareIso qH).hom.app (J'.mapDerivedCategory.obj M) ≫
        R₃.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso d).hom.app M) := by
  let pL := isoWhiskerLeft R₀ c ≪≫ isoWhiskerRight qG I ≪≫ isoWhiskerLeft G' qI
  let pR := isoWhiskerRight qJ H ≪≫ isoWhiskerLeft J' qH ≪≫ isoWhiskerRight d R₃
  have hp : pL = pR := by
    apply Iso.ext
    ext K
    exact hc K
  have hL : (tripleComparison R₀ J H).hom ≫
      Functor.whiskerLeft R₀.mapDerivedCategory
        (Functor.mapDerivedCategorySquareIso c).hom ≫
      Functor.whiskerRight (Functor.mapDerivedCategorySquareIso qG).hom
        I.mapDerivedCategory ≫
      Functor.whiskerLeft G'.mapDerivedCategory
        (Functor.mapDerivedCategorySquareIso qI).hom =
      (Functor.mapDerivedCategoryNatIso pL).hom ≫ (tripleComparison G' I' R₃).hom := by
    rw [reassoc_of% (tripleComparison_left c),
      reassoc_of% (tripleComparison_right qG), tripleComparison_left qI]
    simp only [pL, Functor.mapDerivedCategoryNatIso_trans, Category.assoc]
  have hR : (tripleComparison R₀ J H).hom ≫
      Functor.whiskerRight (Functor.mapDerivedCategorySquareIso qJ).hom
        H.mapDerivedCategory ≫
      Functor.whiskerLeft J'.mapDerivedCategory
        (Functor.mapDerivedCategorySquareIso qH).hom ≫
      Functor.whiskerRight (Functor.mapDerivedCategorySquareIso d).hom
        R₃.mapDerivedCategory =
      (Functor.mapDerivedCategoryNatIso pR).hom ≫ (tripleComparison G' I' R₃).hom := by
    rw [reassoc_of% (tripleComparison_right qJ),
      reassoc_of% (tripleComparison_left qH), tripleComparison_right d]
    simp only [pR, Functor.mapDerivedCategoryNatIso_trans, Category.assoc]
  have h := hL.trans ((congrArg (fun p ↦
    (Functor.mapDerivedCategoryNatIso p).hom ≫ (tripleComparison G' I' R₃).hom) hp).trans hR.symm)
  have h' := (cancel_epi (tripleComparison R₀ J H).hom).1 h
  exact congr_app h' M


end AlgebraicGeometry.ProEtale
