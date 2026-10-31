/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorTensorSiteEquations
import all WeilConjectures.AlgebraicGeometry.ProjectionComparisonEtaleOrigin
import WeilConjectures.SecSmoothPurity.ComparisonTensoratorSignedSymmetry
import all WeilConjectures.AlgebraicGeometry.GeoP1Cohomology
import all WeilConjectures.AlgebraicGeometry.SpDirectImageEtaleMate
import all WeilConjectures.SixFunctors.ComparisonOpenTensorCoherence

/-! # Signed-symmetry pasting for the canonical compact-support comparison. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite

attribute [local implicit_reducible] Scheme.Modules
  Etale.vectorBundlePurityLower Etale.vectorBundlePurityCompactification
  Etale.vectorIntegrationSource
  Etale.derivedTensorRightDerivedLowerShriek
  Etale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
  derivedTensorRightDerivedLowerShriek
  rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar

attribute [-instance] Etale.cartierAbelianPro Etale.cartierAbelianEtale in
private theorem symmetry_component
    (C : Type*) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C]
    [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
    (M N : DerivedCategory C) :
    (((DerivedCategory.canonicalTensorSymmetry C).hom.app M).app N) =
      (derivedTensorKoszulSymmetry C M N).hom := by
  rw [DerivedCategory.canonicalTensorSymmetry_eq]
  rfl

attribute [-instance] Etale.cartierAbelianPro Etale.cartierAbelianEtale in
private theorem module_braiding_eq (A : Type (u + 1)) [CommRing A] :
    (SymmetricCategory.toBraidedCategory (C := ModuleCat.{u + 1} A)) =
      (@ModuleCat.MonoidalCategory.instBraidedCategory A _) := by
  rfl

attribute [-instance] Etale.cartierAbelianPro Etale.cartierAbelianEtale in
private theorem symmetry_koszul_transport
    (B : Type*) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
    [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (b : BraidedCategory B) (hb : b = SymmetricCategory.toBraidedCategory)
    (T : Scheme.{u})
    (M N : DerivedCategory (Sheaf (Scheme.ProEt.topology T) B)) :
    HEq (((symmetry B T).hom.app M).app N)
      (letI : BraidedCategory B := b
       (derivedTensorKoszulSymmetry (Sheaf (Scheme.ProEt.topology T) B) M N).hom) := by
  subst b
  simpa only [symmetry] using
    heq_of_eq (symmetry_component (Sheaf (Scheme.ProEt.topology T) B) M N)

attribute [-instance] Etale.cartierAbelianPro Etale.cartierAbelianEtale in
private theorem comparison_symmetry
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (M N : Etale.DerivedCategoryModule A T) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.map
        (((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) T).hom.app M).app N) ≫
      (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        (ModuleCat.{u + 1} A) N).hom.app M =
    (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A) M).hom.app N ≫
      (((symmetry (ModuleCat.{u + 1} A) T).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M)).app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj N)) := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  have h := comparisonTensorator_signedSymmetry A T M N
  have hb := symmetry_koszul_transport (ModuleCat.{u + 1} A)
    (@ModuleCat.MonoidalCategory.instBraidedCategory A _) (module_braiding_eq A).symm T
    ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M)
    ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj N)
  rw [← eq_of_heq hb] at h
  simpa only [comparison, geoP1Comparison, Iso.app_hom] using h

attribute [-instance] Etale.cartierAbelianPro Etale.cartierAbelianEtale in
private theorem pullback_comparison_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullback A f = comparisonOpenDerivedPullbackIso A f := by
  unfold pullback
  rw [pullComparison_eq, sp_pullback_square, comparisonPullback_transport]
  rfl

attribute [-instance] Etale.cartierAbelianPro Etale.cartierAbelianEtale in
private theorem pullback_symmetry
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (W : Etale.DerivedCategoryModule A X) (K : Etale.DerivedCategoryModule A Y) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
        (((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.app W).app
          ((Etale.ordinaryFinitePullback A f).obj K)) ≫
      (tensorPullbackComparison A f K W).hom =
    (comparisonOpenTensorIso A f W K).hom ≫
      (((symmetry (ModuleCat.{u + 1} A) X).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj W)).app
        ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj K))) := by
  have h := comparison_symmetry A X W ((Etale.ordinaryFinitePullback A f).obj K)
  have hn := ((symmetry (ModuleCat.{u + 1} A) X).hom.app
    ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj W)).naturality
      ((pullback A f).hom.app K)
  unfold tensorPullbackComparison comparisonOpenTensorIso
  rw [← pullback_comparison_eq A f]
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
  simp only [tensorComparison, Iso.app_hom] at h ⊢
  rw [reassoc_of% h]
  exact congrArg
    ((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A) W).hom.app _ ≫ ·) hn.symm

attribute [-instance] Etale.cartierAbelianPro Etale.cartierAbelianEtale in
private theorem bounded_opposite_tensor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (W : Etale.DerivedCategoryModule A X) (K : Etale.DerivedCategoryModule A Y)
    (hM : DerivedCategory.TStructure.t.plus
      (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
        ((Etale.ordinaryFinitePullback A f).obj K)).obj W)) :
    DerivedCategory.TStructure.t.plus
      (projectionComparisonTensor A (f := f) W K) := by
  exact (DerivedCategory.TStructure.t.plus).prop_of_iso
    (((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) X).app
      ((Etale.ordinaryFinitePullback A f).obj K)).app W) hM

attribute [-instance] Etale.cartierAbelianPro Etale.cartierAbelianEtale in
private theorem twist_first_square
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (c : Compactification f)
    (W : Etale.DerivedCategoryModule A X) (K : Etale.DerivedCategoryModule A Y)
    (hW : DerivedCategory.TStructure.t.plus W)
    (hD : DerivedCategory.TStructure.t.plus
      (projectionComparisonTensor A (f := f) W K)) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
        (((Etale.projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app W).app K) ≫
      (compactSupportSiteComparison A c).inv.app ⟨projectionComparisonTensor A (f := f) W K, hD⟩ ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
        (comparisonOpenTensorIso A f W K).hom =
    (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A)
      ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj W)).hom.app
        K ≫
      (((derivedTensor (ModuleCat.{u + 1} A) Y).map
        ((compactSupportSiteComparison A c).inv.app ⟨W, hW⟩)).app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj K)) ≫
      ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj W)).app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj K) := by
  exact compact_projection_square A c W K hW hD

attribute [-instance] Etale.cartierAbelianPro Etale.cartierAbelianEtale in
private theorem compact_comparison_naturality
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (c : Compactification f)
    {M N : Etale.DerivedCategoryModule A X}
    (hM : DerivedCategory.TStructure.t.plus M) (hN : DerivedCategory.TStructure.t.plus N)
    (b : M ⟶ N) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
        ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map b) ≫
      (compactSupportSiteComparison A c).inv.app ⟨N, hN⟩ =
    (compactSupportSiteComparison A c).inv.app ⟨M, hM⟩ ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map b) := by
  exact (compactSupportSiteComparison A c).inv.naturality
    (ObjectProperty.homMk b : ⟨M, hM⟩ ⟶ ⟨N, hN⟩)

attribute [-instance] Etale.cartierAbelianPro Etale.cartierAbelianEtale in
private theorem mapped_pullback_symmetry
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (c : Compactification f)
    (W : Etale.DerivedCategoryModule A X) (K : Etale.DerivedCategoryModule A Y) :
    let L := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
    L.map ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
      (((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.app W).app
        ((Etale.ordinaryFinitePullback A f).obj K))) ≫
      L.map (tensorPullbackComparison A f K W).hom =
    L.map (comparisonOpenTensorIso A f W K).hom ≫
      L.map (((symmetry (ModuleCat.{u + 1} A) X).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj W)).app
        ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj K))) := by
  simpa only [Functor.map_comp] using congrArg
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
    (pullback_symmetry A f W K)

attribute [-instance] Etale.cartierAbelianPro Etale.cartierAbelianEtale in
private theorem target_symmetry_naturality
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (c : Compactification f)
    (W : Etale.DerivedCategoryModule A X) (K : Etale.DerivedCategoryModule A Y)
    (hW : DerivedCategory.TStructure.t.plus W) :
    let Le := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
    let Lp := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
    let VX := (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
    let VY := (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory
    let TY := derivedTensor (ModuleCat.{u + 1} A) Y
    let BW := (compactSupportSiteComparison A c).inv.app ⟨W, hW⟩
    (TY.obj (VY.obj K)).map BW ≫
        ((symmetry (ModuleCat.{u + 1} A) Y).hom.app (VY.obj K)).app (Lp.obj (VX.obj W)) =
      ((symmetry (ModuleCat.{u + 1} A) Y).hom.app (VY.obj K)).app (VY.obj (Le.obj W)) ≫
        (TY.map BW).app (VY.obj K) := by
  exact ((symmetry (ModuleCat.{u + 1} A) Y).hom.app
    ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj K)).naturality
    ((compactSupportSiteComparison A c).inv.app ⟨W, hW⟩)

private theorem symmetry_pasting
    {C : Type*} [Category C] {A B D E F G H I J K L M : C}
    {a : A ⟶ B} {p : B ⟶ D} {l : D ⟶ E} {b : E ⟶ F} {t : F ⟶ G}
    {d : D ⟶ H} {k : H ⟶ F} {o : H ⟶ I} {x : I ⟶ G}
    {u : B ⟶ J} {v : J ⟶ K} {q : K ⟶ I}
    {w : A ⟶ L} {z : L ⟶ J} {r : L ⟶ M} {s : M ⟶ K}
    (hb : l ≫ b = d ≫ k) (hx : k ≫ t = o ≫ x)
    (ht : p ≫ d ≫ o = u ≫ v ≫ q) (hy : a ≫ u = w ≫ z)
    (hs : r ≫ s = z ≫ v) :
    a ≫ p ≫ l ≫ b ≫ t = w ≫ r ≫ s ≫ q ≫ x := by
  rw [reassoc_of% hb, hx, reassoc_of% ht, reassoc_of% hy, ← reassoc_of% hs]

attribute [-instance] Etale.cartierAbelianPro Etale.cartierAbelianEtale in
-- Keep the five local square proofs as lets while matching their object formulas.
set_option cleanup.letToHave false in
/-- The compact-support projection square after changing both tensor orders by the
canonical signed symmetries. Source: Stacks Tags 0944 and 0GL1 for the projection
map and proper/open pasting, Tag 099R for site comparison, and Tag 07A4 for its
monoidal structure.
(blueprint: lem-route-coefficient-first-compact-support-site-square-pasting).

Proof: transport boundedness across the ordinary tensor symmetry and apply the
proved twist-first compact_projection_square at W,K. Naturality of the inverse
compact-support comparison at the ordinary symmetry replaces its target component
by its source component followed by compact support of comparison of symmetry.
The tensorator's compatibility with signed symmetry identifies the square on Y.
On X, naturality of symmetry in the pullback comparison identifies the two tensor
comparison orders. Apply compact support to that square. Finally, naturality of
pro-etale symmetry in the inverse comparison at W supplies the last square.
Associativity and substitution compose these five commutative squares.
All operations are functorial; zero objects and empty schemes require no exceptions.
-/
theorem coefficientFirstCompactSupportPasting
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (c : Compactification f)
    (W : Etale.DerivedCategoryModule A X) (K : Etale.DerivedCategoryModule A Y)
    (hW : DerivedCategory.TStructure.t.plus W)
    (hM : DerivedCategory.TStructure.t.plus
      (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
        ((Etale.ordinaryFinitePullback A f).obj K)).obj W)) :
    let Le := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
    let Lp := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
    let VX := (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
    let VY := (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory
    let TY := derivedTensor (ModuleCat.{u + 1} A) Y
    let PK := (Etale.ordinaryFinitePullback A f).obj K
    let b := ((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.app W).app PK
    let bY := ((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) Y).hom.app K).app (Le.obj W)
    let bX := ((symmetry (ModuleCat.{u + 1} A) X).hom.app (VX.obj W)).app
      ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj (VY.obj K))
    VY.map bY ≫
      VY.map (((Etale.projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app W).app K) ≫
      VY.map (Le.map b) ≫
      (compactSupportSiteComparison A c).inv.app
        ⟨((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj PK).obj W, hM⟩ ≫
      Lp.map (tensorPullbackComparison A f K W).hom =
    (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A) K).hom.app (Le.obj W) ≫
      (TY.obj (VY.obj K)).map ((compactSupportSiteComparison A c).inv.app ⟨W, hW⟩) ≫
      ((symmetry (ModuleCat.{u + 1} A) Y).hom.app (VY.obj K)).app (Lp.obj (VX.obj W)) ≫
      ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app (VX.obj W)).app (VY.obj K) ≫
      Lp.map bX := by
  let Le := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
  let PK := (Etale.ordinaryFinitePullback A f).obj K
  let D := projectionComparisonTensor A (f := f) W K
  have hD := bounded_opposite_tensor A f W K hM
  let b : D ⟶ ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj PK).obj W :=
    ((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.app W).app PK
  have hb := compact_comparison_naturality A f c hD hM b
  have hx := mapped_pullback_symmetry A f c W K
  have hy := comparison_symmetry A Y K (Le.obj W)
  have hs := target_symmetry_naturality A f c W K hW
  have ht := twist_first_square A f c W K hW hD
  dsimp only [Etale.derivedTensorRightDerivedLowerShriek,
    Etale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar,
    derivedTensorRightDerivedLowerShriek,
    rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar,
    Functor.comp_obj, ObjectProperty.ι_obj,
    Functor.whiskeringLeft₂_obj_obj_obj_obj_obj,
    Functor.postcompose₂_obj_obj_obj_obj, Functor.id_obj] at hb hx hy hs ht ⊢
  exact symmetry_pasting hb hx ht hy hs

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
