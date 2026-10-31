/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineAdjunctionMaps
import WeilConjectures.SixFunctors.Etale.Derived.ClosedSupportHom
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorSymmetry
import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided

/-! # Tensor normalization of the coordinate-line counit

Source: current blueprint, sk-prop-an, coordinate-line proof
(blueprint: lem-pur-coordinate-line-counit-tensor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CoordinateLine
open AffineLinePurity VectorIntegrationSite
/-- The derived Koszul braiding with its instances taken from the coefficient category, as
`Etale.derivedBraidedCategory` was stated before it was restricted to finite rings `Λ`. -/
private noncomputable abbrev derivedBraiding (C : Type*) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (X : Scheme.{u}) :
    BraidedCategory (_root_.DerivedCategory (Sheaf X.smallEtaleTopology C)) :=
  _root_.DerivedCategory.braidedCategory' _
attribute [local instance] derivedBraiding
attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor
set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] affineTraceLineCompactification right Etale.affineTraceOpenLeft
  Etale.derivedTensorRightDerivedLowerStar
  Etale.rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar
  Etale.ordinaryFiniteP1Right Etale.ordinaryFiniteTwistedPullback
  Etale.affineTraceOpenAdjunction Etale.ordinaryFinitePullback
  Etale.ordinaryFiniteTensor Etale.derivedTensorRight Etale.ordinaryFiniteProjection

private theorem open_counit_tensor
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (V M : Etale.DerivedCategoryModule A X) :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.map
        (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) j V M).inv ≫
      ((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) j).ofNatIsoRight
        (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j).symm).counit.app
          (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj V).obj M) =
    ((Etale.derivedOpenImmersionLowerShriekProjectionIso
        (ModuleCat.{u + 1} A) j).hom.app
      ((Etale.ordinaryFinitePullback A j).obj V)).app M ≫
    ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).map
      (((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) j).ofNatIsoRight
        (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j).symm).counit.app
          V)).app M := by
  let adj := (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) j).ofNatIsoRight
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j).symm
  have h := Adjunction.projectionMap_app_app_comp_map_counit adj
    (Etale.ordinaryFinitePullback A j)
    (Etale.derivedTensor (ModuleCat.{u + 1} A) U)
    (Etale.derivedTensor (ModuleCat.{u + 1} A) X)
    (Etale.leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} A) j).inv V M
  have hp :
      ((adj.projectionMap (Etale.ordinaryFinitePullback A j)
          (Etale.derivedTensor (ModuleCat.{u + 1} A) U)
          (Etale.derivedTensor (ModuleCat.{u + 1} A) X)
          (Etale.leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} A) j).inv).app
        ((Etale.ordinaryFinitePullback A j).obj V)).app M =
      ((Etale.derivedOpenImmersionLowerShriekProjectionIso
          (ModuleCat.{u + 1} A) j).hom.app
        ((Etale.ordinaryFinitePullback A j).obj V)).app M := by
    simp -implicitDefEqProofs only [Etale.derivedOpenImmersionLowerShriekProjectionIso_hom,
      Etale.derivedOpenImmersionLowerShriekProjectionMap,
      Adjunction.projectionMap_app_app, Adjunction.homEquiv_counit,
      Adjunction.projectionMapTranspose, adj, Adjunction.ofNatIsoRight_unit,
      Adjunction.ofNatIsoRight_counit,
      Etale.mapDerivedCategoryUpperStarDerivedTensorIso]
    simp
    rfl
  simp -implicitDefEqProofs only [Etale.ordinaryFinitePullback] at hp h
  rw [hp] at h
  exact h.symm

private theorem open_counit_tensor_swapped
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (V M : Etale.DerivedCategoryModule A X) :
    let J := (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory
    let L := Etale.ordinaryFinitePullback A j
    let e := ((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) j).ofNatIsoRight
        (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j).symm).counit
    ((Etale.derivedOpenImmersionLowerShriekProjectionIso
        (ModuleCat.{u + 1} A) j).inv.app (L.obj V)).app M ≫
      J.map (β_ (L.obj V) (L.obj M)).hom ≫
      J.map (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) j M V).inv ≫
      e.app (M ⊗ V) =
    (β_ (J.obj (L.obj V)) M).hom ≫ M ◁ e.app V := by
  dsimp only
  let J := (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory
  let L := Etale.ordinaryFinitePullback A j
  let e := ((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) j).ofNatIsoRight
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j).symm).counit
  have hb : (β_ (L.obj V) (L.obj M)).hom ≫
      (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) j M V).inv =
    (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) j V M).inv ≫
      L.map (β_ V M).hom := by
    have h := Etale.derivedPullback_tensorSymmetry A j V M
    change L.map (β_ V M).hom ≫
        (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) j M V).hom =
      (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) j V M).hom ≫
        (β_ (L.obj V) (L.obj M)).hom at h
    apply (cancel_epi (Etale.leftDerivedUpperStarTensorIso
      (ModuleCat.{u + 1} A) j V M).hom).mp
    rw [← Category.assoc, ← h]
    simp -implicitDefEqProofs only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hn : J.map (L.map (β_ V M).hom) ≫ e.app (M ⊗ V) =
      e.app (V ⊗ M) ≫ (β_ V M).hom := e.naturality (β_ V M).hom
  have ht := open_counit_tensor A j V M
  change J.map _ ≫ e.app (V ⊗ M) = _ at ht
  rw [← J.map_comp_assoc, hb, J.map_comp_assoc, hn]
  rw [reassoc_of% ht]
  simp -implicitDefEqProofs only [Iso.inv_hom_id_app_app_assoc]
  exact BraidedCategory.braiding_naturality_left (e.app V) M

private theorem projection_coefficient_naturality
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (q : X ⟶ Y)
    {W V : Etale.DerivedCategoryModule A X} (f : W ⟶ V)
    (K : Etale.DerivedCategoryModule A Y) :
    Etale.ordinaryFiniteProjection A q W K ≫
      (Etale.ordinaryFinitePushforward A q).map
        (((Etale.ordinaryFinitePullback A q).obj K) ◁ f) =
    K ◁ (Etale.ordinaryFinitePushforward A q).map f ≫
      Etale.ordinaryFiniteProjection A q V K := by
  let Q := Etale.ordinaryFinitePushforward A q
  let L := Etale.ordinaryFinitePullback A q
  have hn := NatTrans.congr_app
    ((Etale.rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) q).naturality f) K
  change Q.map f ▷ K ≫
      ((Etale.rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) q).app V).app K =
    ((Etale.rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) q).app W).app K ≫
      Q.map (f ▷ L.obj K) at hn
  simp -implicitDefEqProofs only [Etale.ordinaryFiniteProjection, Category.assoc]
  change (β_ K (Q.obj W)).hom ≫
      ((Etale.rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) q).app W).app K ≫
      Q.map (β_ W (L.obj K)).hom ≫ Q.map ((L.obj K) ◁ f) =
    K ◁ Q.map f ≫ (β_ K (Q.obj V)).hom ≫
      ((Etale.rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) q).app V).app K ≫
      Q.map (β_ V (L.obj K)).hom
  rw [← Q.map_comp, ← BraidedCategory.braiding_naturality_left f (L.obj K),
    Q.map_comp]
  rw [← reassoc_of% hn, ← BraidedCategory.braiding_naturality_right_assoc K (Q.map f)]

private theorem right_comparison_inv
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (B : Scheme.{u}) (K : Etale.DerivedCategoryModule A B) :
    (rightComparison A N hA B).inv.app K =
      ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
        (ProjectiveLine.affineChart B) (ProjectiveLine B ↘ B)
        (AffineSpace PUnit.{u + 1} B ↘ B)
        (ProjectiveLine.affineChart_over B).symm).hom.app K) ▷ (line A N hA B) ≫
      (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A)
        (ProjectiveLine.affineChart B)
        ((Etale.ordinaryFinitePullback A (ProjectiveLine B ↘ B)).obj K)
        ((Etale.ordinaryFiniteLine A N hA (ProjectiveLine B))⟦(2 : ℤ)⟧)).inv := by
  unfold rightComparison
  dsimp only [id, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app,
    Etale.derivedTensorRightCompLeftDerivedUpperStarIso, NatIso.ofComponents_inv_app]
  simp -implicitDefEqProofs only [Category.comp_id]
  rfl

private theorem map_four
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {X₀ X₁ X₂ X₃ X₄ : C}
    (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) (i : X₃ ⟶ X₄)
    (rhs : X₀ ⟶ X₄) (he : f ≫ g ≫ h ≫ i = rhs) :
    F.map f ≫ F.map g ≫ F.map h ≫ F.map i = F.map rhs := by
  rw [← F.map_comp, ← F.map_comp, ← F.map_comp, he]

private theorem mapped_braiding_cancel
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [MonoidalCategory C] [BraidedCategory C]
    (J : C ⥤ D) (Q : D ⥤ E) {X Y : C} (e : X ≅ Y) (W : C) :
    Q.map (J.map (W ◁ e.inv)) ≫ Q.map (J.map (β_ W X).hom) ≫
      Q.map (J.map (e.hom ▷ W)) = Q.map (J.map (β_ W Y).hom) := by
  rw [← Q.map_comp, ← Q.map_comp, ← J.map_comp, ← J.map_comp]
  congr 1
  congr 1
  rw [← Category.assoc, BraidedCategory.braiding_naturality_right]
  simp -implicitDefEqProofs only [Category.assoc, ← comp_whiskerRight, Iso.inv_hom_id,
    id_whiskerRight, Category.comp_id]

private theorem splice_three
    {C : Type*} [Category* C] {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : C}
    {g : X₀ ⟶ X₁} {a : X₁ ⟶ X₂} {b : X₂ ⟶ X₃} {c : X₃ ⟶ X₄}
    {h : X₄ ⟶ X₅} {i : X₅ ⟶ X₆} {d : X₁ ⟶ X₄} {rhs : X₀ ⟶ X₆}
    (hb : a ≫ b ≫ c = d) (ht : g ≫ d ≫ h ≫ i = rhs) :
    g ≫ a ≫ b ≫ c ≫ h ≫ i = rhs := by
  rw [reassoc_of% hb, ht]

private theorem normalized_naturality
    {C : Type*} [Category* C] {X₀ X₁ X₂ X₃ X₄ X₅ : C}
    {a : X₀ ⟶ X₁} {b : X₁ ⟶ X₂} {c : X₀ ⟶ X₃} {d : X₃ ⟶ X₂}
    {e : X₂ ⟶ X₄} {t : X₃ ⟶ X₅} {u : X₅ ⟶ X₄}
    (hn : a ≫ b = c ≫ d) (hd : d ≫ e = t ≫ u) :
    a ≫ b ≫ e = c ≫ t ≫ u := by
  rw [reassoc_of% hn, hd]

private theorem open_counit_tensor_wrapped
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (V M : Etale.DerivedCategoryModule A X) :
    let J := (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory
    let L := Etale.ordinaryFinitePullback A j
    let e := ((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) j).ofNatIsoRight
        (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j).symm).counit
    ((Etale.derivedOpenImmersionLowerShriekProjectionIso
        (ModuleCat.{u + 1} A) j).inv.app (L.obj V)).app M ≫
      J.map (((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) U).hom.app
        (L.obj V)).app (L.obj M)) ≫
      J.map (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) j M V).inv ≫
      e.app (((Etale.ordinaryFiniteTensor A X).obj M).obj V) =
    ((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.app
        (J.obj (L.obj V))).app M ≫
      ((Etale.ordinaryFiniteTensor A X).obj M).map (e.app V) := by
  exact open_counit_tensor_swapped A j V M

private theorem mapped_braiding_cancel_wrapped
    (A : Type (u + 1)) [CommRing A] (B : Scheme.{u})
    {D E : Type*} [Category* D] [Category* E]
    (J : Etale.DerivedCategoryModule A B ⥤ D) (Q : D ⥤ E)
    {X Y : Etale.DerivedCategoryModule A B} (e : X ≅ Y)
    (W : Etale.DerivedCategoryModule A B) :
    Q.map (J.map (((Etale.derivedTensor (ModuleCat.{u + 1} A) B).obj W).map e.inv)) ≫
      Q.map (J.map (((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) B).hom.app
        W).app X)) ≫
      Q.map (J.map (((Etale.derivedTensor (ModuleCat.{u + 1} A) B).map e.hom).app W)) =
    Q.map (J.map (((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) B).hom.app
      W).app Y)) := by
  exact mapped_braiding_cancel J Q e W

private theorem projection_naturality_wrapped
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (q : X ⟶ Y)
    {W V : Etale.DerivedCategoryModule A X} (f : W ⟶ V)
    (K : Etale.DerivedCategoryModule A Y) :
    Etale.ordinaryFiniteProjection A q W K ≫
      (Etale.ordinaryFinitePushforward A q).map
        (((Etale.ordinaryFiniteTensor A X).obj
          ((Etale.ordinaryFinitePullback A q).obj K)).map f) =
    ((Etale.ordinaryFiniteTensor A Y).obj K).map
        ((Etale.ordinaryFinitePushforward A q).map f) ≫
      Etale.ordinaryFiniteProjection A q V K := by
  exact projection_coefficient_naturality A q f K

private theorem right_comparison_inv_wrapped
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (B : Scheme.{u}) (K : Etale.DerivedCategoryModule A B) :
    (rightComparison A N hA B).inv.app K =
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) (AffineSpace PUnit.{u + 1} B)).map
        ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
          (ProjectiveLine.affineChart B) (ProjectiveLine B ↘ B)
          (AffineSpace PUnit.{u + 1} B ↘ B)
          (ProjectiveLine.affineChart_over B).symm).hom.app K)).app (line A N hA B) ≫
      (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A)
        (ProjectiveLine.affineChart B)
        ((Etale.ordinaryFinitePullback A (ProjectiveLine B ↘ B)).obj K)
        ((Etale.ordinaryFiniteLine A N hA (ProjectiveLine B))⟦(2 : ℤ)⟧)).inv := by
  exact right_comparison_inv A N hA B K

@[irreducible]
private def open_line_restriction
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (B : Scheme.{u}) :
    (Etale.affineTraceOpenLeft A B).obj (line A N hA B) ⟶
      (Etale.ordinaryFiniteLine A N hA (ProjectiveLine B))⟦(2 : ℤ)⟧ :=
  (Etale.affineTraceOpenAdjunction A B).counit.app
    ((Etale.ordinaryFiniteLine A N hA (ProjectiveLine B))⟦(2 : ℤ)⟧)

private theorem integration_line_expansion
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (B : Scheme.{u}) [IsNoetherian B] (hN : 0 < N) (hB : IsUnit (N : Γ(B, ⊤))) :
    integration A N hA B hN hB =
      (Etale.ordinaryFinitePushforward A (ProjectiveLine B ↘ B)).map
        (open_line_restriction A N hA B) ≫ Etale.projectiveLineTrace N hN A hA B hB := by
  unfold integration open_line_restriction
  rfl

private theorem open_line_tensor
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (B : Scheme.{u}) (K : Etale.DerivedCategoryModule A B) :
    let j := ProjectiveLine.affineChart B
    let q := ProjectiveLine B ↘ B
    let V := (Etale.ordinaryFiniteLine A N hA (ProjectiveLine B))⟦(2 : ℤ)⟧
    let J := Etale.affineTraceOpenLeft A B
    let L := Etale.ordinaryFinitePullback A j
    let M := (Etale.ordinaryFinitePullback A q).obj K
    ((Etale.derivedOpenImmersionLowerShriekProjectionIso
        (ModuleCat.{u + 1} A) j).inv.app (line A N hA B)).app M ≫
      J.map (((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A)
        (AffineSpace PUnit.{u + 1} B)).hom.app (line A N hA B)).app (L.obj M)) ≫
      J.map (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) j M V).inv ≫
      (Etale.affineTraceOpenAdjunction A B).counit.app
        ((Etale.ordinaryFiniteP1Right A N hA B).obj K) =
    ((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) (ProjectiveLine B)).hom.app
      (J.obj (line A N hA B))).app M ≫
      ((Etale.ordinaryFiniteTensor A (ProjectiveLine B)).obj M).map
        (open_line_restriction A N hA B) := by
  unfold open_line_restriction
  dsimp only [line, Etale.affineTraceOpenLeft, Etale.affineTraceOpenAdjunction,
    Etale.ordinaryFiniteP1Right, Etale.ordinaryFiniteTwistedPullback,
    Etale.derivedTensorRight, Functor.comp_obj, Functor.flip]
  exact open_counit_tensor_wrapped A (ProjectiveLine.affineChart B)
    ((Etale.ordinaryFiniteLine A N hA (ProjectiveLine B))⟦(2 : ℤ)⟧)
    ((Etale.ordinaryFinitePullback A (ProjectiveLine B ↘ B)).obj K)

-- Compare the specified maps through their interfaces, without expanding their data.
set_option allowUnsafeReducibility true in
attribute [local irreducible] Etale.derivedTensor Etale.derivedTensorSymmetry
  Etale.singleFunctorObjUnitIso
  Etale.derivedTensorSingleUnitIso instCategoryDerivedCategory
  DerivedCategory.braidedCategory' Adjunction.ofNatIsoRight
  Etale.derivedOpenImmersionLowerShriekProjectionIso
  Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
  Etale.leftDerivedUpperStarTensorIso Etale.leftDerivedUpperStarComp
  Etale.rightDerivedLowerStarProjectionMap Etale.projectionMapOfCompactification
  Etale.leftDerivedUpperStarCompactificationIso Etale.ordinaryFiniteProjection

set_option allowUnsafeReducibility true in
attribute [local reducible] Etale.ordinaryFiniteTensor Etale.ordinaryFinitePullback
  Etale.ordinaryFiniteP1Right Etale.ordinaryFiniteTwistedPullback
  Etale.derivedTensorRight Etale.affineTraceOpenLeft right

private theorem transported_composite_counit
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ E} {I : E ⥤ D} {R : E ⥤ C}
    (a : F ⊣ G) (b : H ⊣ I) (e : I ⋙ G ≅ R) (K : E) :
    ((Etale.affineTraceComposeAdjunction a b).ofNatIsoRight e).counit.app K =
      (F ⋙ H).map (e.inv.app K) ≫ H.map (a.counit.app (I.obj K)) ≫
        b.counit.app K := by
  rw [Adjunction.ofNatIsoRight_counit]
  simp -implicitDefEqProofs only [NatTrans.comp_app, Functor.whiskerRight_app,
    Etale.affineTraceComposeAdjunction_counit]

private theorem adjunction_counit_expansion
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (B : Scheme.{u}) [IsNoetherian B] (hN : 0 < N) (hB : IsUnit (N : Γ(B, ⊤)))
    (K : Etale.DerivedCategoryModule A B) :
    (adjunction A N hA B hN hB).counit.app K =
      (Etale.affineTraceLineLeft A B).map ((rightComparison A N hA B).inv.app K) ≫
        (Etale.ordinaryFinitePushforward A (ProjectiveLine B ↘ B)).map
          ((Etale.affineTraceOpenAdjunction A B).counit.app
            ((Etale.ordinaryFiniteP1Right A N hA B).obj K)) ≫
        (Etale.projectiveLineTraceDatum N hN A hA B hB).adjunction.counit.app K := by
  unfold adjunction
  exact transported_composite_counit (Etale.affineTraceOpenAdjunction A B)
    (Etale.projectiveLineTraceDatum N hN A hA B hB).adjunction
    (rightComparison A N hA B) K

private theorem projection_counit
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (B : Scheme.{u}) [IsNoetherian B] (hN : 0 < N) (hB : IsUnit (N : Γ(B, ⊤)))
    (K : Etale.DerivedCategoryModule A B) :
    projection A N hA B K ≫ (adjunction A N hA B hN hB).counit.app K =
      ((Etale.ordinaryFiniteTensor A B).obj K).map (integration A N hA B hN hB) ≫
        (Etale.derivedTensorSingleUnitIso K).hom := by
  let V := (Etale.ordinaryFiniteLine A N hA (ProjectiveLine B))⟦(2 : ℤ)⟧
  let q := ProjectiveLine B ↘ B
  let j := ProjectiveLine.affineChart B
  let J := Etale.affineTraceOpenLeft A B
  let Q := Etale.ordinaryFinitePushforward A q
  let L := Etale.ordinaryFinitePullback A j
  let D := Etale.projectiveLineTraceDatum N hN A hA B hB
  have ht := open_line_tensor A N hA B K
  have hd := D.counit_normalization K
  have hb := mapped_braiding_cancel_wrapped A (AffineSpace PUnit.{u + 1} B) J Q
    ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) j q
      (AffineSpace PUnit.{u + 1} B ↘ B) (ProjectiveLine.affineChart_over B).symm).app K)
    (line A N hA B)
  have hqt := map_four Q _ _ _ _ _ ht
  have hc := splice_three hb hqt
  rw [adjunction_counit_expansion]
  unfold projection
  rw [integration_line_expansion]
  simp -implicitDefEqProofs only [right_comparison_inv_wrapped,
    Functor.comp_map,
    Functor.map_comp, Category.assoc]
  simp only [Iso.app_hom, Iso.app_inv, j, q, J, Q,
    Etale.ordinaryFinitePullback, Etale.ordinaryFiniteP1Right,
    Etale.ordinaryFiniteTwistedPullback, Etale.derivedTensorRight,
    Functor.comp_obj, Functor.flip] at hc ⊢
  rw [reassoc_of% hc]
  simp -implicitDefEqProofs only [Functor.map_comp, Category.assoc]
  change Etale.ordinaryFiniteProjection A q V K ≫ D.adjunction.counit.app K = _ at hd
  have hn := normalized_naturality
    (projection_naturality_wrapped A q
      (open_line_restriction A N hA B) K) hd
  simpa -implicitDefEqProofs only [Etale.ordinaryFiniteProjection,
    Etale.projectiveLineTrace,
    Etale.ordinaryFiniteTensor, Etale.ordinaryFinitePullback,
    Etale.affineTraceOpenLeft, Functor.comp_obj, Functor.id_obj,
    j, q, J, Q, L, V, D, Category.assoc] using hn

/-- The actual open/projective counit is inverse projection followed by tensor trace.
Source: current blueprint, cor-pur-affine-space-zero-section-purity.proof.md,
ordinary affine-line adjunction paragraph
(blueprint: lem-pur-coordinate-line-counit-tensor).

Proof: put q=P1_B→B, j=A1_B→P1_B and V=A(1)[2]. Transport the composite
j! ⊣ j* and Rq* ⊣ q*(-) tensor V along the tensor/pullback comparison.
Its counit is Rq*(e_{q*K tensor V}) followed by the projective counit.
The unit-defined open projection and its counit identity identify this with
proper projection followed by 1 tensor Rq*(e_V), then the projective counit.
Apply its prescribed normalization and proper projection naturality at e_V.
The two pullback-composition maps cancel and the two specified tensor symmetries
produce precisely projection below. The finite-coefficient proper projection
and the open projection are invertible, so their composite is invertible.
Take its canonical asIso, cancel its hom, and obtain the asserted inverse formula.
This uses no flatness of A, includes the zero ring and the empty base, and works
for arbitrary K (the displayed finite-Tor domain is only the consumer's domain). -/
theorem coordinate_line_counit_tensor
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (B : Scheme.{u}) [IsNoetherian B] (hN : 0 < N) (hB : IsUnit (N : Γ(B, ⊤)))
    (K : Etale.DerivedCategoryModule A B)
    (_hK : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) B K) :
    CounitNormalization A N hA B hN hB K := by
  have hi : IsIso (projection A N hA B K) := by
    unfold projection
    have := Etale.isIso_rightDerivedLowerStarProjectionMap_of_finite A
      (ProjectiveLine B ↘ B)
    infer_instance
  have := hi
  refine ⟨asIso (projection A N hA B K), rfl, ?_⟩
  apply (cancel_epi (projection A N hA B K)).mp
  change projection A N hA B K ≫ _ =
    (asIso (projection A N hA B K)).hom ≫ (asIso (projection A N hA B K)).inv ≫ _
  rw [Iso.hom_inv_id_assoc]
  exact projection_counit A N hA B hN hB K

end AlgebraicGeometry.ProEtale.CoordinateLine
