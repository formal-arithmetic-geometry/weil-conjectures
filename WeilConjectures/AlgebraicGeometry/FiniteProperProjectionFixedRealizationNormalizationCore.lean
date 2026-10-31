/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteProjectionFixedCoordinates
import all WeilConjectures.AlgebraicGeometry.FiniteProjectionIterationRealization
import all WeilConjectures.AlgebraicGeometry.IdentityFactorCoefficientComparison
import all WeilConjectures.SixFunctors.RefinementProjectionLocalTensor
import WeilConjectures.SixFunctors.ProEtaleDerivedPullbackTensorComposition
import WeilConjectures.SixFunctors.ProEtale.RingSheaf.UpperStarSquare
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

/-! # Coordinate projection equation for proper normalization -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u u'
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Functor
namespace WeilConjectures.CompactSupportFiniteProjection

section
attribute [local instance] Sheaf.monoidalCategory
attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor AlgebraicGeometry.ProEtale.derivedTensor
section
attribute [local irreducible] Functor.leftDerivedFunctorIsoMapDerivedCategory
  DerivedCategory instCategoryDerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions upperStar lowerStar openImmersionLowerShriek
  leftDerivedUpperStarComp leftDerivedUpperStarId leftDerivedUpperStarTensorComparison
  leftDerivedUpperStarTensorNatIso mapDerivedCategoryUpperStarDerivedTensorIso
  leftDerivedUpperStarIsoMapDerivedCategory Functor.mapDerivedCategoryNatIso
  Functor.mapDerivedCategoryIdIso
attribute [local implicit_reducible] Compactification.ofIsProper


attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem identity_left_to_map
    (B : Type u') [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
    [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B] (X : Scheme.{u})
    (M : DerivedCategory (Sheaf (ProEt.topology X) B)) :
    (leftDerivedUpperStarId B X).hom.app M =
      (leftDerivedUpperStarIsoMapDerivedCategory B (𝟙 X)).hom.app M ≫
        (Functor.mapDerivedCategoryNatIso (upperStarId B X)).hom.app M ≫
        (Functor.mapDerivedCategoryIdIso _).hom.app M := by
  have hi : leftDerivedUpperStarId B X =
      leftDerivedUpperStarIsoMapDerivedCategory B (𝟙 X) ≪≫
        Functor.mapDerivedCategoryNatIso (upperStarId B X) ≪≫
          Functor.mapDerivedCategoryIdIso _ := by
    simp only [leftDerivedUpperStarId, Functor.leftDerivedFunctorNatIso,
      leftDerivedUpperStarIsoMapDerivedCategory, Iso.trans_assoc, Iso.symm_self_id_assoc]
  simpa only [Iso.trans_hom, NatTrans.comp_app] using
    congrArg (fun e ↦ e.hom.app M) hi


end

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem unit_of_identity_counit
    {A : Type*} [Category A] {J P : A ⥤ A} (adj : J ⊣ P)
    (d : J ≅ 𝟭 A) (e : P ≅ 𝟭 A)
    (hc : ∀ Z, d.inv.app (P.obj Z) ≫ adj.counit.app Z = e.hom.app Z) (Z : A) :
    adj.unit.app Z ≫ P.map (d.hom.app Z) ≫ e.hom.app Z = 𝟙 Z := by
  have hc' (W : A) : adj.counit.app W = d.hom.app (P.obj W) ≫ e.hom.app W := by
    apply (cancel_epi (d.inv.app (P.obj W))).1
    simpa only [Iso.inv_hom_id_app_assoc] using hc W
  have hn := d.hom.naturality (adj.unit.app Z)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.id_obj] at hn
  have hu : adj.unit.app Z ≫ e.hom.app (J.obj Z) = d.inv.app Z := by
    apply (cancel_epi (d.hom.app Z)).1
    rw [← Category.assoc, ← hn, Category.assoc]
    change J.map (adj.unit.app Z) ≫ d.hom.app (P.obj (J.obj Z)) ≫
      e.hom.app (J.obj Z) = _
    rw [← hc']
    simp only [Iso.hom_inv_id_app]
    exact adj.left_triangle_components Z
  have hn2 : P.map (d.hom.app Z) ≫ e.hom.app Z =
      e.hom.app (J.obj Z) ≫ d.hom.app Z := e.hom.naturality _
  rw [hn2, ← Category.assoc, hu, d.inv_hom_id_app]
  rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem open_unit_identity
    (B : Type u') [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
    [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B]
    (X : Scheme.{u})
    (M : DerivedCategory (Sheaf (ProEt.topology X) B)) :
    let P := (upperStar B (𝟙 X)).mapDerivedCategory
    let d := Functor.mapDerivedCategoryNatIso (openImmersionLowerShriekIdIso B X) ≪≫
      Functor.mapDerivedCategoryIdIso _
    let e := Functor.mapDerivedCategoryNatIso (upperStarId B X) ≪≫
      Functor.mapDerivedCategoryIdIso _
    (derivedOpenImmersionLowerShriekUpperStarAdjunction B (𝟙 X)).unit.app M ≫
      P.map (d.hom.app M) ≫ e.hom.app M = 𝟙 _ := by
  let adj := openImmersionLowerShriekUpperStarAdjunction B (𝟙 X)
  let d := openImmersionLowerShriekIdIso B X
  let e := upperStarId B X
  have hd (Z : Sheaf (ProEt.topology X) B) :
      d.inv.app ((upperStar B (𝟙 X)).obj Z) ≫ adj.counit.app Z = e.hom.app Z := by
    have h := adj.leftAdjointUniq_ofNatIsoRight_inv_app_comp_counit e Z
    rw [FixProjectionCompactification.left_id_fixed] at h
    exact h
  exact unit_of_identity_counit adj.mapDerivedCategoryAdjunction
    (Functor.mapDerivedCategoryNatIso d ≪≫ Functor.mapDerivedCategoryIdIso _)
    (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso _)
    (adj.mapDerivedCategoryAdjunction_counit_app_of_iso d e hd) M

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem inverse_comparison
    {C : Type*} [Category C] {X Y Z : C}
    {a : X ⟶ Y} {b : Y ⟶ X} {c : Y ⟶ Z} {d : X ⟶ Z}
    (hi : b ≫ a = 𝟙 Y) (h : a ≫ c = d) : b ≫ d = c := by
  rw [← h, ← Category.assoc, hi, Category.id_comp]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem identity_mixed_paste
    {C : Type*} [Category C] (T : C ⥤ C ⥤ C)
    {M PM FM FN U FU PU : C}
    (a : M ⟶ PM) (b : PM ⟶ FM) (d : FM ≅ M)
    (c : (T.obj FM).obj FN ⟶ FU) (l : FU ⟶ PU) (e : PU ≅ U)
    (t : (T.obj M).obj FN ⟶ U)
    (hm : a ≫ b = d.inv)
    (ht : c ≫ l ≫ e.hom = (T.map d.hom).app FN ≫ t) :
    (T.map a).app FN ≫ (T.map b).app FN ≫ c ≫ l = t ≫ e.inv := by
  have hm' : (T.map a).app FN ≫ (T.map b).app FN = (T.map d.inv).app FN := by
    rw [← NatTrans.comp_app, ← T.map_comp, hm]
  apply (cancel_mono e.hom).1
  simp only [Category.assoc, e.inv_hom_id, Category.comp_id]
  rw [reassoc_of% hm', ht]
  rw [← Category.assoc, ← NatTrans.comp_app, ← T.map_comp, d.inv_hom_id,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]


attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem generic_identity_mixed_tensor
    (B : Type u') [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
    [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B]
    (X : Scheme.{u})
    (M N : DerivedCategory (Sheaf (ProEt.topology X) B))
    (hleft : ∀ Z : DerivedCategory (Sheaf (ProEt.topology X) B),
      (leftDerivedUpperStarId B X).hom.app Z =
        (leftDerivedUpperStarIsoMapDerivedCategory B (𝟙 X)).hom.app Z ≫
          (Functor.mapDerivedCategoryNatIso (upperStarId B X)).hom.app Z ≫
          (Functor.mapDerivedCategoryIdIso _).hom.app Z)
    (htensor :
      ((leftDerivedUpperStarTensorComparison B (𝟙 X)).app M).app N ≫
        ((derivedTensor B X).map ((leftDerivedUpperStarId B X).hom.app M)).app
          ((upperStar B (𝟙 X)).leftDerivedFunctor.obj N) ≫
        ((derivedTensor B X).obj M).map ((leftDerivedUpperStarId B X).hom.app N) =
      (leftDerivedUpperStarId B X).hom.app (((derivedTensor B X).obj M).obj N)) :
    let F := (upperStar B (𝟙 X)).leftDerivedFunctor
    let e := Functor.mapDerivedCategoryNatIso (upperStarId B X) ≪≫
      Functor.mapDerivedCategoryIdIso _
    ((derivedTensor B X).map (e.inv.app M)).app (F.obj N) ≫
      ((mapDerivedCategoryUpperStarDerivedTensorIso B (𝟙 X)).hom.app M).app N =
        ((derivedTensor B X).obj M).map ((leftDerivedUpperStarId B X).hom.app N) ≫
          e.inv.app (((derivedTensor B X).obj M).obj N) := by
  let T := derivedTensor B X
  let F := (upperStar B (𝟙 X)).leftDerivedFunctor
  let l := leftDerivedUpperStarIsoMapDerivedCategory B (𝟙 X)
  let e := Functor.mapDerivedCategoryNatIso (upperStarId B X) ≪≫
    Functor.mapDerivedCategoryIdIso _
  let d := leftDerivedUpperStarId B X
  have hl : l ≪≫ e = d := by
    apply Iso.ext
    apply NatTrans.ext
    funext Z
    exact (hleft Z).symm
  have hli : e.inv.app M ≫ l.inv.app M = d.inv.app M := by
    simpa only [Iso.trans_inv, NatTrans.comp_app] using
      congrArg (fun z ↦ z.inv.app M) hl
  have hlh : l.hom.app (((T.obj M).obj N)) ≫ e.hom.app (((T.obj M).obj N)) =
      d.hom.app (((T.obj M).obj N)) := by
    exact congrArg (fun z ↦ z.hom.app (((T.obj M).obj N))) hl
  have hd : ((leftDerivedUpperStarTensorNatIso B (𝟙 X)).inv.app M).app N ≫
      d.hom.app (((T.obj M).obj N)) =
        (T.map (d.hom.app M)).app (F.obj N) ≫ (T.obj M).map (d.hom.app N) := by
    exact inverse_comparison
      (Iso.inv_hom_id_app_app (leftDerivedUpperStarTensorNatIso B (𝟙 X)) M N)
      (by simpa only [leftDerivedUpperStarTensorNatIso_hom, Category.assoc] using
        htensor)
  have ht : ((leftDerivedUpperStarTensorNatIso B (𝟙 X)).inv.app M).app N ≫
      l.hom.app ((T.obj M).obj N) ≫ e.hom.app ((T.obj M).obj N) =
        (T.map (d.hom.app M)).app (F.obj N) ≫ (T.obj M).map (d.hom.app N) := by
    rw [hlh]
    exact hd
  have hh := identity_mixed_paste T (e.inv.app M) (l.inv.app M) (d.app M)
    (((leftDerivedUpperStarTensorNatIso B (𝟙 X)).inv.app M).app N)
    (l.hom.app ((T.obj M).obj N)) (e.app ((T.obj M).obj N))
    ((T.obj M).map (d.hom.app N)) hli ht
  have hop : ((mapDerivedCategoryUpperStarDerivedTensorIso B (𝟙 X)).hom.app M).app N =
      ((T.map (l.inv.app M)).app (F.obj N)) ≫
        ((leftDerivedUpperStarTensorNatIso B (𝟙 X)).inv.app M).app N ≫
        l.hom.app ((T.obj M).obj N) := by
    rfl
  rw [hop]
  exact hh



attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem generic_identity_open_projection
    (B : Type u') [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
    [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B]
    (X : Scheme.{u})
    (M N : DerivedCategory (Sheaf (ProEt.topology X) B))
    (hunit : ∀ Z : DerivedCategory (Sheaf (ProEt.topology X) B),
      (derivedOpenImmersionLowerShriekUpperStarAdjunction B (𝟙 X)).unit.app Z ≫
        (upperStar B (𝟙 X)).mapDerivedCategory.map
          (((Functor.mapDerivedCategoryNatIso (openImmersionLowerShriekIdIso B X) ≪≫
      Functor.mapDerivedCategoryIdIso _)).hom.app Z) ≫
        (Functor.mapDerivedCategoryNatIso (upperStarId B X) ≪≫
          Functor.mapDerivedCategoryIdIso _).hom.app Z = 𝟙 _)
    (hmixed :
      ((derivedTensor B X).map
        ((Functor.mapDerivedCategoryNatIso (upperStarId B X) ≪≫
          Functor.mapDerivedCategoryIdIso _).inv.app M)).app
          ((upperStar B (𝟙 X)).leftDerivedFunctor.obj N) ≫
        ((mapDerivedCategoryUpperStarDerivedTensorIso B (𝟙 X)).hom.app M).app N =
      ((derivedTensor B X).obj M).map ((leftDerivedUpperStarId B X).hom.app N) ≫
        (Functor.mapDerivedCategoryNatIso (upperStarId B X) ≪≫
          Functor.mapDerivedCategoryIdIso _).inv.app (((derivedTensor B X).obj M).obj N)) :
    let J := (openImmersionLowerShriek B (𝟙 X)).mapDerivedCategory
    let d := (Functor.mapDerivedCategoryNatIso (openImmersionLowerShriekIdIso B X) ≪≫
      Functor.mapDerivedCategoryIdIso _)
    ((derivedOpenImmersionLowerShriekProjectionIso B (𝟙 X)).inv.app M).app N ≫
      J.map (((derivedTensor B X).obj M).map ((leftDerivedUpperStarId B X).hom.app N)) ≫
      d.hom.app (((derivedTensor B X).obj M).obj N) =
        ((derivedTensor B X).map (d.hom.app M)).app N := by
  let J := (openImmersionLowerShriek B (𝟙 X)).mapDerivedCategory
  let P := (upperStar B (𝟙 X)).mapDerivedCategory
  let F := (upperStar B (𝟙 X)).leftDerivedFunctor
  let T := derivedTensor B X
  let d := (Functor.mapDerivedCategoryNatIso (openImmersionLowerShriekIdIso B X) ≪≫
      Functor.mapDerivedCategoryIdIso _)
  let e := Functor.mapDerivedCategoryNatIso (upperStarId B X) ≪≫
    Functor.mapDerivedCategoryIdIso _
  let adj := derivedOpenImmersionLowerShriekUpperStarAdjunction B (𝟙 X)
  let t := (T.obj M).map ((leftDerivedUpperStarId B X).hom.app N)
  have hu (Z : DerivedCategory (Sheaf (ProEt.topology X) B)) :
      adj.unit.app Z ≫ P.map (d.hom.app Z) = e.inv.app Z := by
    apply (cancel_mono (e.hom.app Z)).1
    simpa only [Category.assoc, e.inv_hom_id_app] using hunit Z
  have hh : J.map t ≫ d.hom.app (((T.obj M).obj N)) =
      ((derivedOpenImmersionLowerShriekProjectionIso B (𝟙 X)).hom.app M).app N ≫
        (T.map (d.hom.app M)).app N := by
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    simp only [Functor.map_comp]
    have ht := adj.unit.naturality t
    dsimp only [Functor.comp_map, Functor.id_map] at ht
    rw [← reassoc_of% ht, hu]
    rw [derivedOpenImmersionLowerShriekProjectionIso_hom,
      derivedOpenImmersionLowerShriekProjectionMap]
    have hp := adj.unit_app_comp_map_projectionMap_app_app F T T
      (mapDerivedCategoryUpperStarDerivedTensorIso B (𝟙 X)).hom M N
    erw [reassoc_of% hp]
    simp only [Adjunction.projectionMapTranspose_app_app]
    have hn := congr_app
      ((mapDerivedCategoryUpperStarDerivedTensorIso B (𝟙 X)).hom.naturality
        (d.hom.app M)) N
    dsimp only [Functor.postcompose₂, Functor.whiskeringLeft₂,
      Functor.whiskeringLeft, Functor.whiskeringRight, Functor.comp_map,
      Functor.comp_obj, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.id_obj] at hn
    simp only [Category.assoc]
    erw [← hn]
    erw [← NatTrans.comp_app_assoc, ← T.map_comp, hu]
    exact hmixed.symm
  change ((derivedOpenImmersionLowerShriekProjectionIso B (𝟙 X)).inv.app M).app N ≫
    J.map t ≫ d.hom.app (((T.obj M).obj N)) = (T.map (d.hom.app M)).app N
  rw [hh, Iso.inv_hom_id_app_app_assoc]


attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian HasDerivedCategory.ofHasKInjectiveResolutions

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem identity_open_projection
    (B : Type u') [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
    [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B]
    (X : Scheme.{u})
    (M N : DerivedCategory (Sheaf (ProEt.topology X) B))
    (htensor : ∀ M N : DerivedCategory (Sheaf (ProEt.topology X) B),
      ((leftDerivedUpperStarTensorComparison B (𝟙 X)).app M).app N ≫
        ((derivedTensor B X).map ((leftDerivedUpperStarId B X).hom.app M)).app
          ((upperStar B (𝟙 X)).leftDerivedFunctor.obj N) ≫
        ((derivedTensor B X).obj M).map ((leftDerivedUpperStarId B X).hom.app N) =
      (leftDerivedUpperStarId B X).hom.app (((derivedTensor B X).obj M).obj N)) :
    let J := (openImmersionLowerShriek B (𝟙 X)).mapDerivedCategory
    let d := Functor.mapDerivedCategoryNatIso
      (openImmersionLowerShriekIdIso B X) ≪≫ Functor.mapDerivedCategoryIdIso _
    ((derivedOpenImmersionLowerShriekProjectionIso B (𝟙 X)).inv.app M).app N ≫
      J.map (((AlgebraicGeometry.ProEtale.derivedTensor B X).obj M).map
        ((leftDerivedUpperStarId B X).hom.app N)) ≫
      d.hom.app (((AlgebraicGeometry.ProEtale.derivedTensor B X).obj M).obj N) =
        ((AlgebraicGeometry.ProEtale.derivedTensor B X).map (d.hom.app M)).app N := by
  exact generic_identity_open_projection B X M N (open_unit_identity B X)
    (generic_identity_mixed_tensor B X M N (identity_left_to_map B X) (htensor M N))
end

section
attribute [local instance] Sheaf.monoidalCategory
attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor AlgebraicGeometry.ProEtale.derivedTensor
attribute [local irreducible]
  DerivedCategory instCategoryDerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions upperStar lowerStar openImmersionLowerShriek
  leftDerivedUpperStarComp leftDerivedUpperStarId leftDerivedUpperStarTensorComparison
  leftDerivedUpperStarTensorNatIso mapDerivedCategoryUpperStarDerivedTensorIso
  leftDerivedUpperStarIsoMapDerivedCategory Functor.mapDerivedCategoryNatIso
  Functor.mapDerivedCategoryIdIso
attribute [local implicit_reducible] Compactification.ofIsProper
  derivedTensorRightDerivedLowerStar rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar
  derivedTensorRightDerivedLowerShriek rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem pull_congr_hom (B : Type u') [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
    [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B] {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    (leftDerivedUpperStarCongr B h).hom =
      (eqToIso (congrArg (fun h ↦ (upperStar B h).leftDerivedFunctor) h)).hom := by
  cases h
  rfl

attribute [local irreducible] projectionMapOfCompactification
  leftDerivedUpperStarCompactificationIso derivedOpenImmersionLowerShriekProjectionIso
  rightDerivedLowerStarProjectionMap identityFactorFixedProper

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem direct_projection_naturality
    (B : Type u') [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
    [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M M' : DerivedCategory (Sheaf (ProEt.topology X) B)} (a : M ⟶ M')
    (N : DerivedCategory (Sheaf (ProEt.topology Y) B)) :
    ((AlgebraicGeometry.ProEtale.derivedTensor B Y).map
      ((lowerStar B f).rightDerivedFunctor.map a)).app N ≫
        ((rightDerivedLowerStarProjectionMap B f).app M').app N =
      ((rightDerivedLowerStarProjectionMap B f).app M).app N ≫
        (lowerStar B f).rightDerivedFunctor.map
          (((AlgebraicGeometry.ProEtale.derivedTensor B X).map a).app
            ((upperStar B f).leftDerivedFunctor.obj N)) := by
  exact congr_app ((rightDerivedLowerStarProjectionMap B f).naturality a) N

private theorem whisker_identity_app {A B : Type*} [Category A] [Category B]
    (J : A ⥤ A) (Q : A ⥤ B) (d : J ≅ 𝟭 A) (M : A) :
    (Functor.isoWhiskerRight d Q ≪≫ Functor.leftUnitor Q).hom.app M =
      Q.map (d.hom.app M) := by
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app]
  exact Category.comp_id _

private theorem projection_identity_paste {A B : Type*} [Category A] [Category B]
    (T : A ⥤ A ⥤ A) (U : B ⥤ B ⥤ B) (J : A ⥤ A) (P : B ⥤ A) (Q : A ⥤ B)
    (d : J ≅ 𝟭 A)
    (π : ∀ m nn, (U.obj (Q.obj m)).obj nn ⟶ Q.obj ((T.obj m).obj (P.obj nn)))
    (M : A) (N : B) {W : A}
    (a : (T.obj (J.obj M)).obj (P.obj N) ⟶ W)
    (b : W ⟶ J.obj ((T.obj M).obj (P.obj N)))
    (hab : a ≫ b ≫ d.hom.app ((T.obj M).obj (P.obj N)) =
      (T.map (d.hom.app M)).app (P.obj N))
    (hn : (U.map (Q.map (d.hom.app M))).app N ≫ π M N =
      π (J.obj M) N ≫ Q.map ((T.map (d.hom.app M)).app (P.obj N))) :
    π (J.obj M) N ≫ Q.map a ≫ Q.map b ≫
        Q.map (d.hom.app ((T.obj M).obj (P.obj N))) =
      (U.map (Q.map (d.hom.app M))).app N ≫ π M N := by
  simp only [← Q.map_comp]
  rw [hab]
  exact hn.symm

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem projection_paste_retype
    (B : Type u') [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
    [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B]
    {X Z Y X' Z' Y' : Scheme.{u}} (hX : X = X') (hZ : Z = Z') (hY : Y = Y')
    {i : X ⟶ Z} {i' : X' ⟶ Z'} [IsOpenImmersion i] [IsOpenImmersion i']
    {g : Z ⟶ Y} {g' : Z' ⟶ Y'} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (hi : HEq i i') (hg : HEq g g') (hf : HEq f f')
    {M : DerivedCategory (Sheaf (ProEt.topology X) B)}
    {M' : DerivedCategory (Sheaf (ProEt.topology X') B)} (hM : HEq M M')
    {N : DerivedCategory (Sheaf (ProEt.topology Y) B)}
    {N' : DerivedCategory (Sheaf (ProEt.topology Y') B)} (hN : HEq N N')
    {a : (upperStar B i).leftDerivedFunctor.obj
      ((upperStar B g).leftDerivedFunctor.obj N) ⟶ (upperStar B f).leftDerivedFunctor.obj N}
    {a' : (upperStar B i').leftDerivedFunctor.obj
      ((upperStar B g').leftDerivedFunctor.obj N') ⟶ (upperStar B f').leftDerivedFunctor.obj N'}
    (ha : HEq a a') :
    HEq
      (((rightDerivedLowerStarProjectionMap B g).app
        ((openImmersionLowerShriek B i).mapDerivedCategory.obj M)).app N ≫
        (lowerStar B g).rightDerivedFunctor.map
          (((derivedOpenImmersionLowerShriekProjectionIso B i).inv.app M).app
            ((upperStar B g).leftDerivedFunctor.obj N)) ≫
        (lowerStar B g).rightDerivedFunctor.map
          ((openImmersionLowerShriek B i).mapDerivedCategory.map
            (((derivedTensor B X).obj M).map a)))
      (((rightDerivedLowerStarProjectionMap B g').app
        ((openImmersionLowerShriek B i').mapDerivedCategory.obj M')).app N' ≫
        (lowerStar B g').rightDerivedFunctor.map
          (((derivedOpenImmersionLowerShriekProjectionIso B i').inv.app M').app
            ((upperStar B g').leftDerivedFunctor.obj N')) ≫
        (lowerStar B g').rightDerivedFunctor.map
          ((openImmersionLowerShriek B i').mapDerivedCategory.map
            (((derivedTensor B X').obj M').map a'))) := by
  cases hX
  cases hZ
  cases hY
  have hi := eq_of_heq hi
  have hg := eq_of_heq hg
  have hf := eq_of_heq hf
  subst i'
  subst g'
  subst f'
  have hM := eq_of_heq hM
  have hN := eq_of_heq hN
  subst M'
  subst N'
  have ha := eq_of_heq ha
  subst a'
  rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem proper_normalized_expansion
    (B : Type u') [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
    [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (M : DerivedCategory (Sheaf (ProEt.topology X) B))
    (N : DerivedCategory (Sheaf (ProEt.topology Y) B)) :
    ((projectionMapOfCompactification B (.ofIsProper f)).app M).app N =
      ((rightDerivedLowerStarProjectionMap B f).app
        ((openImmersionLowerShriek B (𝟙 X)).mapDerivedCategory.obj M)).app N ≫
      (lowerStar B f).rightDerivedFunctor.map
        (((derivedOpenImmersionLowerShriekProjectionIso B (𝟙 X)).inv.app M).app
          ((upperStar B f).leftDerivedFunctor.obj N)) ≫
      (lowerStar B f).rightDerivedFunctor.map
        ((openImmersionLowerShriek B (𝟙 X)).mapDerivedCategory.map
          (((derivedTensor B X).obj M).map
            ((leftDerivedUpperStarId B X).hom.app
              ((upperStar B f).leftDerivedFunctor.obj N)))) := by
  have hp : (leftDerivedUpperStarCompactificationIso B (.ofIsProper f)).hom.app N =
      (leftDerivedUpperStarId B X).hom.app ((upperStar B f).leftDerivedFunctor.obj N) := by
    simp only [leftDerivedUpperStarCompactificationIso, Compactification.ofIsProper,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
    apply (cancel_epi ((leftDerivedUpperStarComp B (𝟙 X) f).hom.app N)).1
    rw [Iso.hom_inv_id_app_assoc]
    simpa only [pull_congr_hom] using
      (leftDerivedUpperStarComp_id_left_app (A := B) f N).symm
  have hh := projection_paste_retype B
    (X := X) (Z := (Compactification.ofIsProper f).Z) (Y := Y)
    (X' := X) (Z' := X) (Y' := Y) rfl rfl rfl
    (i := (Compactification.ofIsProper f).i) (i' := 𝟙 X)
    (g := (Compactification.ofIsProper f).g) (g' := f) (f := f) (f' := f)
    (heq_of_eq (show (Compactification.ofIsProper f).i = 𝟙 X from rfl))
    (heq_of_eq (show (Compactification.ofIsProper f).g = f from rfl)) HEq.rfl
    (M := M) (M' := M) HEq.rfl (N := N) (N' := N) HEq.rfl (heq_of_eq hp)
  rw [projectionMapOfCompactification_app_app]
  exact eq_of_heq hh

set_option maxHeartbeats 400000 in
-- Keep the derived adjunction comparisons abstract while elaborating the paste.
attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem proper_fixed_projection
    (B : Type u') [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
    [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (M : DerivedCategory (Sheaf (ProEt.topology X) B))
    (N : DerivedCategory (Sheaf (ProEt.topology Y) B))
    (hId : ∀ (M N : DerivedCategory
      (Sheaf (ProEt.topology X) B)),
    let J := (openImmersionLowerShriek B (𝟙 X)).mapDerivedCategory
    let d := Functor.mapDerivedCategoryNatIso
      (openImmersionLowerShriekIdIso B X) ≪≫ Functor.mapDerivedCategoryIdIso _
    ((derivedOpenImmersionLowerShriekProjectionIso B (𝟙 X)).inv.app M).app N ≫
      J.map (((AlgebraicGeometry.ProEtale.derivedTensor B X).obj M).map
        ((leftDerivedUpperStarId B X).hom.app N)) ≫
      d.hom.app (((AlgebraicGeometry.ProEtale.derivedTensor B X).obj M).obj N) =
        ((AlgebraicGeometry.ProEtale.derivedTensor B X).map (d.hom.app M)).app N) :
    let d := Functor.mapDerivedCategoryNatIso
      (openImmersionLowerShriekIdIso B X) ≪≫ Functor.mapDerivedCategoryIdIso _
    let e := Functor.isoWhiskerRight d (lowerStar B f).rightDerivedFunctor ≪≫
      Functor.leftUnitor (lowerStar B f).rightDerivedFunctor
    let T := AlgebraicGeometry.ProEtale.derivedTensor B X
    ((projectionMapOfCompactification B (.ofIsProper f)).app M).app N ≫
      e.hom.app ((T.obj M).obj ((upperStar B f).leftDerivedFunctor.obj N)) =
    ((AlgebraicGeometry.ProEtale.derivedTensor B Y).map (e.hom.app M)).app N ≫
      ((rightDerivedLowerStarProjectionMap B f).app M).app N := by
  let P := (upperStar B f).leftDerivedFunctor
  let Q := (lowerStar B f).rightDerivedFunctor
  let T := AlgebraicGeometry.ProEtale.derivedTensor B X
  let d := Functor.mapDerivedCategoryNatIso
    (openImmersionLowerShriekIdIso B X) ≪≫ Functor.mapDerivedCategoryIdIso _
  let J := (openImmersionLowerShriek B (𝟙 X)).mapDerivedCategory
  let U := derivedTensor B Y
  let π (m : DerivedCategory (Sheaf (ProEt.topology X) B))
      (nn : DerivedCategory (Sheaf (ProEt.topology Y) B)) :=
    ((rightDerivedLowerStarProjectionMap B f).app m).app nn
  let a := ((derivedOpenImmersionLowerShriekProjectionIso B (𝟙 X)).inv.app M).app (P.obj N)
  let b := J.map ((T.obj M).map ((leftDerivedUpperStarId B X).hom.app (P.obj N)))
  dsimp only
  rw [proper_normalized_expansion, whisker_identity_app, whisker_identity_app]
  simp only [Category.assoc]
  apply projection_identity_paste T U J P Q d π M N a b
  · exact hId M (P.obj N)
  · exact direct_projection_naturality B f (d.hom.app M) N

private theorem dependent_congr {A : Sort*} {B : A → Sort*}
    (F : ∀ a, B a) {a a' : A} (h : a = a') : HEq (F a) (F a') := by
  cases h
  rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem direct_functor_retype
    (B : Type u') [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B]
    {X Y X' Y' : Scheme.{u}} (hX : X = X') (hY : Y = Y')
    {g : X ⟶ Y} {g' : X' ⟶ Y'} (hg : HEq g g') :
    HEq (lowerStar B g).rightDerivedFunctor (lowerStar B g').rightDerivedFunctor := by
  cases hX
  cases hY
  have hg := eq_of_heq hg
  subst g'
  rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem proper_whisker_component
    (B : Type u') [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (M : DerivedCategory (Sheaf (ProEt.topology X) B)) :
    let d := Functor.mapDerivedCategoryNatIso
      (openImmersionLowerShriekIdIso B X) ≪≫ Functor.mapDerivedCategoryIdIso _
    let Q : DerivedCategory (Sheaf (ProEt.topology X) B) ⥤
        DerivedCategory (Sheaf (ProEt.topology Y) B) :=
      (lowerStar B (Compactification.ofIsProper f).g).rightDerivedFunctor
    (Functor.isoWhiskerRight d Q ≪≫ Functor.leftUnitor Q).hom.app M =
      (Functor.isoWhiskerRight d (lowerStar B f).rightDerivedFunctor ≪≫
        Functor.leftUnitor (lowerStar B f).rightDerivedFunctor).hom.app M := by
  let d := Functor.mapDerivedCategoryNatIso
    (openImmersionLowerShriekIdIso B X) ≪≫ Functor.mapDerivedCategoryIdIso _
  have hQ : (show DerivedCategory (Sheaf (ProEt.topology X) B) ⥤
      DerivedCategory (Sheaf (ProEt.topology Y) B) from
      (lowerStar B (Compactification.ofIsProper f).g).rightDerivedFunctor) =
        (lowerStar B f).rightDerivedFunctor :=
    eq_of_heq (direct_functor_retype B
      (X := (Compactification.ofIsProper f).Z) (X' := X) (Y := Y) (Y' := Y)
      rfl rfl (heq_of_eq (show (Compactification.ofIsProper f).g = f from rfl)))
  dsimp only
  exact eq_of_heq (dependent_congr
    (fun Q : DerivedCategory (Sheaf (ProEt.topology X) B) ⥤
        DerivedCategory (Sheaf (ProEt.topology Y) B) ↦
      (Functor.isoWhiskerRight d Q ≪≫ Functor.leftUnitor Q).hom.app M) hQ)

open AlgebraicGeometry.ProEtale.AmbientProperOpen
open AlgebraicGeometry.ProEtale.AmbientProperOpen.RefinementProjection
open AlgebraicGeometry.ProEtale.AmbientProperOpen.RefinementProjection.Words

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem pull_congr_index
    (B : Type u') [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
    [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B]
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    leftDerivedUpperStarCongr B h =
      indexIso (fun g : X ⟶ Y ↦ (upperStar B g).leftDerivedFunctor) h := by
  cases h
  rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem tensor_identity_normalized
    (B : Type u') [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
    [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B] (X : Scheme.{u})
    [NatTrans.IsMonoidal (upperStarComp B (𝟙 X) (𝟙 X)).inv]
    (M N : DerivedCategory (Sheaf (ProEt.topology X) B)) :
    ((leftDerivedUpperStarTensorComparison B (𝟙 X)).app M).app N ≫
      ((derivedTensor B X).map ((leftDerivedUpperStarId B X).hom.app M)).app
        ((upperStar B (𝟙 X)).leftDerivedFunctor.obj N) ≫
      ((derivedTensor B X).obj M).map ((leftDerivedUpperStarId B X).hom.app N) =
    (leftDerivedUpperStarId B X).hom.app (((derivedTensor B X).obj M).obj N) := by
  let P := fun g : X ⟶ X ↦ (upperStar B g).leftDerivedFunctor
  let e := leftDerivedUpperStarId B X
  have hu := AmbientProperOpen.RefinementProjection.tensor_identity_unit_curried
    (derivedTensor B X) P (fun g ↦ leftDerivedUpperStarTensorNatIso B g)
    (Category.id_comp (𝟙 X)) e (leftDerivedUpperStarComp B (𝟙 X) (𝟙 X)) (by
      intro K
      change (indexIso P (Category.id_comp (𝟙 X)).symm).hom.app K ≫
        (leftDerivedUpperStarComp B (𝟙 X) (𝟙 X)).hom.app K ≫
        (P (𝟙 X)).map (e.hom.app K) = 𝟙 _
      have h := leftDerivedUpperStarComp_id_right_app (A := B) (𝟙 X) K
      rw [pull_congr_index] at h
      rw [h, indexIso_trans_app]
      simp only [indexIso_refl, Iso.refl_hom, NatTrans.id_app]) (by
      intro K L
      have h := leftDerivedUpperStarTensorComparison_comp B (𝟙 X) (𝟙 X) K L
      simp only [leftDerivedUpperStarTensorIso_hom] at h
      simp only [leftDerivedUpperStarTensorNatIso_hom]
      dsimp only [Functor.whiskeringLeft₂, Functor.whiskeringLeft, Functor.whiskeringRight,
        Functor.postcompose₂, Functor.comp_obj, Functor.id_obj] at h ⊢
      exact h)
  simpa only [leftDerivedUpperStarTensorNatIso_hom] using hu M N


private theorem proper_fixed_projection_canonical
    (B : Type u') [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
    [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (M : DerivedCategory (Sheaf (ProEt.topology X) B))
    (N : DerivedCategory (Sheaf (ProEt.topology Y) B))
    [NatTrans.IsMonoidal (upperStarComp B (𝟙 X) (𝟙 X)).inv] :
    let d := Functor.mapDerivedCategoryNatIso
      (openImmersionLowerShriekIdIso B X) ≪≫ Functor.mapDerivedCategoryIdIso _
    let e := Functor.isoWhiskerRight d (lowerStar B f).rightDerivedFunctor ≪≫
      Functor.leftUnitor (lowerStar B f).rightDerivedFunctor
    let T := AlgebraicGeometry.ProEtale.derivedTensor B X
    ((projectionMapOfCompactification B (.ofIsProper f)).app M).app N ≫
      e.hom.app ((T.obj M).obj ((upperStar B f).leftDerivedFunctor.obj N)) =
    ((AlgebraicGeometry.ProEtale.derivedTensor B Y).map (e.hom.app M)).app N ≫
      ((rightDerivedLowerStarProjectionMap B f).app M).app N := by
  exact proper_fixed_projection B f M N (fun m nn ↦
    identity_open_projection B X m nn (tensor_identity_normalized B X))


/-- Expose the two tensor endpoints before specializing the coefficient ring. -/
private noncomputable def directProjectionCoordinates
    (B : Type u') [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
    [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : DerivedCategory (Sheaf (ProEt.topology X) B))
    (N : DerivedCategory (Sheaf (ProEt.topology Y) B)) :
    ((AlgebraicGeometry.ProEtale.derivedTensor B Y).obj
      ((lowerStar B f).rightDerivedFunctor.obj M)).obj N ⟶
    (lowerStar B f).rightDerivedFunctor.obj
      (((AlgebraicGeometry.ProEtale.derivedTensor B X).obj M).obj
        ((upperStar B f).leftDerivedFunctor.obj N)) :=
  ((rightDerivedLowerStarProjectionMap B f).app M).app N

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem proper_projection_module
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (M : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (N : DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} Λ))) :
    let e := identityFactorFixedProper Λ f
    projectionTensorCoordinateComponent (ModuleCat.{u + 1} Λ) (.ofIsProper f) M N ≫
      e.hom.app (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj M).obj
        ((upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor.obj N)) =
    ((derivedTensor (ModuleCat.{u + 1} Λ) Y).map (e.hom.app M)).app N ≫
      directProjectionCoordinates (ModuleCat.{u + 1} Λ) f M N := by
  let : NatTrans.IsMonoidal
      (upperStarComp (ModuleCat.{u + 1} Λ) (𝟙 X) (𝟙 X)).inv :=
    RingSheaf.isMonoidal_upperStarComp_inv _ _
  dsimp only
  let d := Functor.mapDerivedCategoryNatIso
    (openImmersionLowerShriekIdIso (ModuleCat.{u + 1} Λ) X) ≪≫
      Functor.mapDerivedCategoryIdIso _
  let e' := Functor.isoWhiskerRight d (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor ≪≫
    Functor.leftUnitor (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor
  have he (m : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))) :
      (identityFactorFixedProper Λ f).hom.app m = e'.hom.app m := by
    simpa only [e', d, identityFactorFixedProper] using
      proper_whisker_component (ModuleCat.{u + 1} Λ) f m
  rw [he, he]
  simpa only [projectionTensorCoordinateComponent, directProjectionCoordinates] using
    proper_fixed_projection_canonical (ModuleCat.{u + 1} Λ) f M N

end

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

attribute [local implicit_reducible] coordinates realization sixFunctorFiniteRealization
  Compactification.ofIsProper fixedDirect supportRealization fixedSupportRealization
  directCoordinates sfIntrinsicDerivedEquivalence
  FixProjectionCompactification.openRealization sixFunctorFiniteSupport
  sfAmbientCompactSupportCandidate sfIntrinsicCompactSupport
attribute [local irreducible] sfIntrinsicModuleEquivalence Functor.mapDerivedCategory
  Functor.rightDerivedFunctor Functor.leftDerivedFunctor DerivedCategory
  instCategoryDerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions sfIntrinsicCompactSupportComparison

attribute [local implicit_reducible]
  derivedTensorRightDerivedLowerStar rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar
  derivedTensorRightDerivedLowerShriek rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar

attribute [local implicit_reducible] fixedTensor fixedDerivedPull fixedComponent
attribute [local instance] Sheaf.monoidalCategory
attribute [local irreducible] AlgebraicGeometry.ProEtale.derivedTensor upperStar lowerStar
  openImmersionLowerShriek Functor.mapDerivedCategoryNatIso Functor.mapDerivedCategoryIdIso
-- Specialize tensor coherence with abstract derived inputs before applying coordinates.
attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem finite_fixed_proper_projection
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (M : DerivedCategory (Sheaf (ProEt.topology X.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))))
    (N : DerivedCategory (Sheaf (ProEt.topology Y.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))))) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let c := Compactification.ofIsProper f.hom.left
    let e := identityFactorFixedProper
      (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)) f.hom.left
    fixedComponent (C := C) (E := E) (n := n) (hn := hn) f c M N ≫
        e.hom.app (((fixedTensor (C := C) (E := E) (n := n) X).obj M).obj
          ((fixedDerivedPull (C := C) (E := E) (n := n) f).obj N)) =
      ((fixedTensor (C := C) (E := E) (n := n) Y).map (e.hom.app M)).app N ≫
        directProjectionCoordinates
          (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
            f.hom.left M N := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  dsimp only
  simpa only [fixedComponent, fixedTensor, fixedDerivedPull] using
    proper_projection_module
      (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)) f.hom.left M N


private theorem proper_coefficient_square (A : Type u) [CommRing A] [Finite A]
    {U V : Scheme.{u}} (f : U ⟶ V) [IsProper f]
    (M : DerivedCategory (Sheaf (ProEt.topology U)
      (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :
    (sfIntrinsicCompactSupportComparison A (.ofIsProper f)).hom.app M ≫
      (sfIntrinsicDerivedEquivalence V A).functor.map
        ((identityFactorFixedProper (ULift.{u + 1} A) f).hom.app M) =
      (sixFunctorProperCandidateIso A f).hom.app
        ((sfIntrinsicDerivedEquivalence U A).functor.obj M) ≫
      (sfIntrinsicDerivedDirectImageComparison f A).hom.app M := by
  rw [FixProjectionCompactification.supportComparison_app,
    FixProjectionCompactification.properCandidate_app]
  let v := (Functor.mapDerivedCategoryNatIso
    (openImmersionLowerShriekIdIso (ModuleCat.{u + 1} (ULift.{u + 1} A)) U) ≪≫
      Functor.mapDerivedCategoryIdIso _).hom.app M
  have hn := (sfIntrinsicDerivedDirectImageComparison f A).hom.naturality v
  dsimp only [Functor.comp_map] at hn
  have ho := FixProjectionCompactification.open_identity_square A U M
  dsimp only [Compactification.ofIsProper]
  simp only [identityFactorFixedProper, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Category.assoc]
  erw [Category.comp_id]
  erw [← hn, ← Functor.map_comp_assoc]
  exact congrArg (fun t ↦ (proEtaleConstantDerivedDirectImage f A).map t ≫
    (sfIntrinsicDerivedDirectImageComparison f A).hom.app M) ho

private theorem proper_support_coordinates
    (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (K : sixFunctorFiniteCategory D C E n hn X) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    (coordinates (C := C) (E := E) (n := n) (hn := hn) Y).map
        ((S.finite.properIdentity f).hom.app K) ≫ (directCoordinates S f K).hom =
      (fixedSupportRealization S f (.ofIsProper f.hom.left) K).hom ≫
        (identityFactorFixedProper (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))
          f.hom.left).hom.app
            ((coordinates (C := C) (E := E) (n := n) (hn := hn) X).obj K) := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let A := Padic.coefficientExtensionRing C.l E n
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
  let c := Compactification.ofIsProper f.hom.left
  let Q := proEtaleConstantDerivedDirectImage f.hom.left A
  let F := sfIntrinsicCompactSupport c A
  let k := RX.inverse.obj K.obj
  let v := RX.counitIso.inv.app K.obj
  let d := (S.finiteDirectImage f).app K ≪≫ Q.mapIso (RX.counitIso.app K.obj).symm ≪≫
    (sfIntrinsicDerivedDirectImageComparison f.hom.left A).app k
  let e := identityFactorFixedProper (ULift.{u + 1} A) f.hom.left
  have hp := congrArg Iso.hom (S.finiteProperNormalization f K)
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom] at hp
  have hc := proper_coefficient_square A f.hom.left k
  have hnat := (sixFunctorProperCandidateIso A f.hom.left).hom.naturality v
  have h : ((S.finite.properIdentity f).hom.app K).hom ≫ d.hom =
      (supportRealization S f c K).hom ≫ RY.functor.map (e.hom.app k) := by
    let s := (S.finiteSupport f c).hom.app K
    let t := (sfIntrinsicDerivedDirectImageComparison f.hom.left A).hom.app k
    let p := (sixFunctorProperCandidateIso A f.hom.left).hom
    let w := (sfIntrinsicCompactSupportComparison A c).hom.app k
    change ((S.finite.properIdentity f).hom.app K).hom ≫
      ((S.finiteDirectImage f).hom.app K ≫ Q.map v ≫ t) =
      (s ≫ F.map v ≫ w) ≫ RY.functor.map (e.hom.app k)
    calc
      _ = s ≫ p.app K.obj ≫ Q.map v ≫ t := by
        simpa only [s, p, A, c, ObjectProperty.ι_map, Category.assoc] using
          congrArg (fun z ↦ z ≫ Q.map v ≫ t) hp
      _ = s ≫ F.map v ≫ p.app (RX.functor.obj k) ≫ t := by
        simpa only [p, F, Q, k, Functor.id_obj, Functor.comp_obj, Category.assoc] using
          congrArg (fun z ↦ s ≫ z ≫ t) hnat.symm
      _ = _ := by
        simpa only [p, t, w, e, RX, RY, realization, sixFunctorFiniteRealization,
          Category.assoc] using
          congrArg (fun z ↦ s ≫ F.map v ≫ z) hc.symm
  have hm := congrArg RY.inverse.map h
  simp only [Functor.map_comp] at hm
  have hu : RY.inverse.map (RY.functor.map (e.hom.app k)) ≫ RY.unitIso.inv.app _ =
      RY.unitIso.inv.app _ ≫ e.hom.app k := RY.unitIso.inv.naturality _
  change RY.inverse.map ((S.finite.properIdentity f).hom.app K).hom ≫
      (RY.inverse.map d.hom ≫ RY.unitIso.inv.app _) =
    (RY.inverse.map (supportRealization S f c K).hom ≫ RY.unitIso.inv.app _) ≫
      e.hom.app k
  simpa only [Category.assoc, hu, sfFixedCompactSupport, c, k, RX, A, Functor.comp_obj,
    Compactification.ofIsProper] using
    congrArg (fun t ↦ t ≫ RY.unitIso.inv.app _) hm

set_option maxHeartbeats 800000 in
-- The comparison paste elaborates several derived functors without unfolding their constructions.
/--
The coordinate image of the expanded proper component is the fixed direct-image
projection map after the source and target tensor comparisons.  This is the
coefficient-normalization part of the proper-factor calculation: expand the
proper identity, use `finiteProperNormalization`, and cancel the realization
units and the direct/tensor comparison isomorphisms.  The remaining adjunction
transpose is handled by the theorem in the importing module.
Source: prop-sf-pf-coherence.proof.md, proper-factor paragraph.
(blueprint: lem-sf-finite-proper-projection-fixed-realization-normalization)
Proof: expand `properComponent` and `component`; apply the finite proper
normalization and the normalized direct adjunction mate.  Naturality of the
realization unit and of the tensor comparison cancels the coefficient units,
leaving the fixed direct-image projection map on the displayed object.
The identity compactification, identity inputs, and zero morphisms reduce by
functoriality and the unit/counit identities.
-/
theorem properComponent_fixed_realization_coordinate_projection
    (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let pc :=
      ((partialTensor S Y).map ((S.finite.properIdentity f).inv.app K)).app L ≫
        component S f (.ofIsProper f.hom.left) K L ≫
        (S.finite.properIdentity f).hom.app
          (((partialTensor S X).obj K).obj ((torPull S f).obj L))
    (coordinates (C := C) (E := E) (n := n) (hn := hn) Y).map pc ≫
        (directCoordinates S f (((partialTensor S X).obj K).obj ((torPull S f).obj L))).hom ≫
        (fixedDirect (C := C) (E := E) (n := n) f).map (targetCoordinates S f K L).hom =
      (directTensorCoordinates S f K L).hom ≫
      ((AlgebraicGeometry.ProEtale.rightDerivedLowerStarProjectionMap
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
          f.hom.left).app
            ((coordinates (C := C) (E := E) (n := n) (hn := hn) X).obj K)).app
              ((realization (C := C) (E := E) (n := n) (hn := hn) Y).inverse.obj L.obj) := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let c := Compactification.ofIsProper f.hom.left
  let JX := coordinates (C := C) (E := E) (n := n) (hn := hn) X
  let JY := coordinates (C := C) (E := E) (n := n) (hn := hn) Y
  let F := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) c
  let TY := fixedTensor (C := C) (E := E) (n := n) Y
  let N := (realization (C := C) (E := E) (n := n) (hn := hn) Y).inverse.obj L.obj
  let B := ((partialTensor S X).obj K).obj ((torPull S f).obj L)
  let b := targetCoordinates S f K L
  let e := AlgebraicGeometry.ProEtale.identityFactorFixedProper
    (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)) f.hom.left
  have hn' (M : sixFunctorFiniteCategory D C E n hn X) :
      JY.map ((S.finite.properIdentity f).hom.app M) ≫ (directCoordinates S f M).hom =
        (fixedSupportRealization S f c M).hom ≫ e.hom.app (JX.obj M) := by
    exact proper_support_coordinates S f M
  have hcomp : JY.map (component S f c K L) ≫
      (fixedSupportRealization S f c B).hom ≫ F.map b.hom =
    (tensorCoordinates S Y ((S.finite.support f c).obj K) L).hom ≫
      (TY.map (fixedSupportRealization S f c K).hom).app N ≫
      fixedComponent (C := C) (E := E) (n := n) (hn := hn) f c (JX.obj K) N := by
    exact fixed_component_realization S f c K L
  have hpf :
      fixedComponent (C := C) (E := E) (n := n) (hn := hn) f c (JX.obj K) N ≫
          e.hom.app (((fixedTensor (C := C) (E := E) (n := n) X).obj (JX.obj K)).obj
            ((fixedDerivedPull (C := C) (E := E) (n := n) f).obj N)) =
        (TY.map (e.hom.app (JX.obj K))).app N ≫
          directProjectionCoordinates
            (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
              f.hom.left (JX.obj K) N := by
    exact finite_fixed_proper_projection f (JX.obj K) N
  dsimp only
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn']
  erw [← e.hom.naturality b.hom]
  erw [reassoc_of% hcomp, hpf]
  erw [reassoc_of% (tensorCoordinates_naturality S Y
    ((S.finite.properIdentity f).inv.app K) L)]
  have ht :
      (TY.map (JY.map ((S.finite.properIdentity f).inv.app K))).app N ≫
        (TY.map (fixedSupportRealization S f c K).hom).app N ≫
        (TY.map (e.hom.app (JX.obj K))).app N =
      (TY.map (directCoordinates S f K).hom).app N := by
    rw [← NatTrans.comp_app, ← TY.map_comp, ← NatTrans.comp_app, ← TY.map_comp]
    congr 2
    rw [← hn', ← JY.map_comp_assoc]
    simp only [Iso.inv_hom_id_app, JY.map_id, Category.id_comp]
  rw [reassoc_of% ht]
  simp only [directProjectionCoordinates, directTensorCoordinates, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom,
    Category.assoc, TY, JX, N]

end WeilConjectures.CompactSupportFiniteProjection
