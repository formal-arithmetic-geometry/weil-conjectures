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
public import WeilConjectures.CategoryTheory.MateCube
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientDerivedFunctorAPI
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TensorPullbackMateNormalization

/-! Normalization data for the scalar/open exchange argument. -/

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

section ExactCoherence
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
  [Abelian C] [Abelian D] [Abelian E] [Abelian F]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [HasDerivedCategory F]
  (L : C ⥤ D) (M : D ⥤ E) (N : E ⥤ F)
  [L.Additive] [M.Additive] [N.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits M] [PreservesFiniteColimits M]
  [PreservesFiniteLimits N] [PreservesFiniteColimits N]

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

variable {L M N}
  {D' : Type*} [Category D'] [Abelian D'] [HasDerivedCategory D']
  {L' : C ⥤ D'} {M' : D' ⥤ E}
  [L'.Additive] [M'.Additive]
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [PreservesFiniteLimits M'] [PreservesFiniteColimits M']

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

variable {E' : Type*} [Category E'] [Abelian E'] [HasDerivedCategory E']
  {M'' : D ⥤ E'} {N' : E' ⥤ F}
  [M''.Additive] [N'.Additive]
  [PreservesFiniteLimits M''] [PreservesFiniteColimits M'']
  [PreservesFiniteLimits N'] [PreservesFiniteColimits N']

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

end ExactCoherence

section DerivedCube
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*}
  [Category C₀] [Category C₁] [Category C₂] [Category C₃]
  [Category D₀] [Category D₁] [Category D₂] [Category D₃]
  [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃]
  [Abelian D₀] [Abelian D₁] [Abelian D₂] [Abelian D₃]
  [HasDerivedCategory C₀] [HasDerivedCategory C₁]
  [HasDerivedCategory C₂] [HasDerivedCategory C₃]
  [HasDerivedCategory D₀] [HasDerivedCategory D₁]
  [HasDerivedCategory D₂] [HasDerivedCategory D₃]
  {R₀ : D₀ ⥤ C₀} {R₁ : D₁ ⥤ C₁} {R₂ : D₂ ⥤ C₂} {R₃ : D₃ ⥤ C₃}
  {J : C₀ ⥤ C₁} {H : C₁ ⥤ C₃} {G : C₀ ⥤ C₂} {I : C₂ ⥤ C₃}
  {J' : D₀ ⥤ D₁} {H' : D₁ ⥤ D₃} {G' : D₀ ⥤ D₂} {I' : D₂ ⥤ D₃}
  [R₀.Additive] [R₁.Additive] [R₂.Additive] [R₃.Additive]
  [J.Additive] [H.Additive] [G.Additive] [I.Additive]
  [J'.Additive] [H'.Additive] [G'.Additive] [I'.Additive]
  [PreservesFiniteLimits R₀] [PreservesFiniteColimits R₀]
  [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
  [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
  [PreservesFiniteLimits R₃] [PreservesFiniteColimits R₃]
  [PreservesFiniteLimits J] [PreservesFiniteColimits J]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits I] [PreservesFiniteColimits I]
  [PreservesFiniteLimits J'] [PreservesFiniteColimits J']
  [PreservesFiniteLimits H'] [PreservesFiniteColimits H']
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  [PreservesFiniteLimits I'] [PreservesFiniteColimits I']

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

end DerivedCube

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

private theorem restriction_pullback_comp
    {U V W : Scheme.{u}} (h : U ⟶ V) (k : V ⟶ W) :
    NatTrans.SquareCompatible
      (T := D(Mod.comap (coefficientMap a W)))
      (T' := D(Mod.comap (coefficientMap a U)))
      (derivedComapLeftDerivedUpperStarIso a (h ≫ k)).symm
      (Functor.pasteSquareIso (derivedComapLeftDerivedUpperStarIso a k).symm
        (derivedComapLeftDerivedUpperStarIso a h).symm)
      (coefficientDerivedUpperStarComp B h k).hom
      (coefficientDerivedUpperStarComp A h k).hom := by
  intro N
  have hc := derivedComapLeftDerivedUpperStarIso_comp_hom_app a h k N
  apply (cancel_mono ((Functor.pasteSquareIso
    (derivedComapLeftDerivedUpperStarIso a k).symm
    (derivedComapLeftDerivedUpperStarIso a h).symm).inv.app N)).1
  simp only [Category.assoc, Iso.hom_inv_id_app]
  simp only [Functor.pasteSquareIso_inv_app, Iso.symm_inv, Iso.symm_hom]
  change _ = _ ≫ (CondensedRing.leftDerivedUpperStarComp A h k).hom.app _ ≫ _ ≫ _
  rw [hc]
  simp only [Iso.inv_hom_id_app_assoc]
  exact Category.comp_id _

private theorem restriction_pullback_congr
    {U V : Scheme.{u}} {h k : U ⟶ V} (e : h = k) :
    NatTrans.SquareCompatible
      (T := D(Mod.comap (coefficientMap a V)))
      (T' := D(Mod.comap (coefficientMap a U)))
      (derivedComapLeftDerivedUpperStarIso a h).symm
      (derivedComapLeftDerivedUpperStarIso a k).symm
      (eqToIso (congrArg (coefficientDerivedUpperStar B) e)).hom
      (eqToIso (congrArg (coefficientDerivedUpperStar A) e)).hom := by
  subst k
  simp only [eqToIso_refl, Iso.refl_hom]
  exact NatTrans.SquareCompatible.id _

private theorem restriction_pullback_square {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' f' f g) :
    NatTrans.SquareCompatible
      (T := D(Mod.comap (coefficientMap a Y)))
      (T' := D(Mod.comap (coefficientMap a X')))
      (Functor.pasteSquareIso (derivedComapLeftDerivedUpperStarIso a g).symm
        (derivedComapLeftDerivedUpperStarIso a f').symm)
      (Functor.pasteSquareIso (derivedComapLeftDerivedUpperStarIso a f).symm
        (derivedComapLeftDerivedUpperStarIso a g').symm)
      (coefficientAmbientSquare B sq).hom (coefficientAmbientSquare A sq).hom := by
  rw [coefficientAmbientSquare_eq, coefficientAmbientSquare_eq,
    coefficientIsoTransThree_eq, coefficientIsoTransThree_eq]
  exact (restriction_pullback_comp a f' g).inv.comp
    ((restriction_pullback_congr a sq.w.symm).comp (restriction_pullback_comp a g' f))

private theorem square_inverse
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {U : C ⥤ C'} {V : D ⥤ D'}
    {F G : C ⥤ D} {F' G' : C' ⥤ D'}
    (iF : F ⋙ V ≅ U ⋙ F') (iG : G ⋙ V ≅ U ⋙ G')
    (α : F ⟶ G) (α' : F' ⟶ G')
    (h : NatTrans.SquareCompatible iF iG α α') (M : C) :
    α'.app (U.obj M) ≫ iG.inv.app M = iF.inv.app M ≫ V.map (α.app M) := by
  apply (cancel_epi (iF.hom.app M)).1
  rw [← Category.assoc, ← h M]
  simp only [Category.assoc, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc]
  exact Category.comp_id _

/-- Tensor extension commutes with the specified pullback square for condensed rings.
Source: the final compatibility paragraph of the latest blueprint's
`lem-fix-compact-support-coefficient-change`; Stacks Tags 07A4 and 0G7E.
(blueprint: lem-fix-tensor-pullback-square)
Proof: restriction of scalars respects the derived pullback compositors. Apply this
on both paths and their equality transport to get the restriction cube. The four
extension/restriction adjunctions turn that cube into the tensor cube, by the old
scalarMateCube proof. The nonflat derived comparison has exactly this mate by
tensorPullbackMateNormalization. No flatness, nonempty scheme,
or nonzero coefficient hypothesis is used. -/
theorem tensorPullbackSquare
    {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    (sq : OpenImmersionSquare gU j' j g)
    (N : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj A X))) :
    let S (T : Scheme.{u}) := L(Mod.extendScalars (coefficientMap a T))
    let P (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        [MonObj R] [IsCommMonObj R] {V W : Scheme.{u}} (f : V ⟶ W) :=
      coefficientDerivedUpperStar R f
    let c (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        [MonObj R] [IsCommMonObj R] := coefficientAmbientSquare R sq.toCommSq
    let lam {V W : Scheme.{u}} (f : V ⟶ W) := derivedUpperStarExtendScalarsIso a f
    (S U').map ((c A).inv.app N) ≫
      (lam j').hom.app ((P A g).obj N) ≫ (P B j').map ((lam g).hom.app N) =
    (lam gU).hom.app ((P A j).obj N) ≫
      (P B gU).map ((lam j).hom.app N) ≫ (c B).inv.app ((S X).obj N) := by
  let q {V W : Scheme.{u}} (f : V ⟶ W) :=
    (derivedComapLeftDerivedUpperStarIso a f).hom
  have hc (M : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj B X))) :=
    square_inverse _ _ _ _ (restriction_pullback_square a sq.toCommSq).inv M
  simp only [Functor.pasteSquareIso_inv_app, Iso.symm_inv, Category.assoc] at hc
  let adj (T : Scheme.{u}) :=
    Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a T)
  have hm := scalarMateCube (adj X) (adj U) (adj X') (adj U')
    (q j) (q gU) (q g) (q j')
    (coefficientAmbientSquare A sq.toCommSq).inv
    (coefficientAmbientSquare B sq.toCommSq).inv hc N
  have hmate {V W : Scheme.{u}} (f : V ⟶ W) :
      ((mateEquiv (adj W) (adj V)).symm (TwoSquare.mk _ _ _ _ (q f))).natTrans =
        (derivedUpperStarExtendScalarsIso a f).hom := by
    rw [show TwoSquare.mk _ _ _ _ (q f) =
      mateEquiv (adj W) (adj V)
        (TwoSquare.mk _ _ _ _ (derivedUpperStarExtendScalarsIso a f).hom) from
      (tensorPullbackMateNormalization a f).symm]
    simp only [Equiv.symm_apply_apply]
  simpa only [hmate, coefficientDerivedUpperStar] using hm

end AlgebraicGeometry.ProEtale
