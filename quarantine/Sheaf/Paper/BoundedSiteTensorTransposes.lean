/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q101
-/
module

public import Sheaf.Paper.BoundedSiteAdjunctionTranspose
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin
import all Sheaf.Paper.BoundedSiteAdjunctionTranspose
import all Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin
import Sheaf.Paper.SiteTensorUnitEvaluation
import WeilConjectures.CategoryTheory.Monoidal.DerivedSymmetric

/-! # Bounded site comparison of tensor evaluation transposes

Source: current blueprint, lem-pur-co-smooth-etale-locality, proof Steps 1 and 3;
Stacks Project, Tag 0B65 (blueprint: lem-pur-bounded-site-tensor-transposes).

## Main statements

* `boundedSiteTensorTransposes`: arbitrary evaluation and reversed-factor comparison.
* `boundedSiteTensorTransposes_dualizing`: the counit-defined theta specialization.
* `boundedSiteTensorTransposes_natural`: source and target naturality of the Hom-chain.

The evaluation is arbitrary. Only the displayed finite-Tor projection components
are inverted. The pro-etale transpose is the specified bounded-origin Hom-chain,
transported along the canonical tensor/pullback identification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] Functor.mapDerivedCategory
  _root_.DerivedCategory.braidedCategory' compactSupportSiteComparison

section Arrows
variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
variable (H : Etale.DerivedCategoryModule A Y ⥤ Etale.DerivedCategoryModule A X)
variable (adj : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ H)
variable (M : Etale.DerivedCategoryModule A X) (K : Etale.DerivedCategoryModule A Y)

/-- The compared evaluation e_p = C_Y(e) B_M inverse, with its canonical unit map.
Source: blueprint proof Steps 1 and 3
(blueprint: lem-pur-bounded-site-tensor-transposes). -/
@[irreducible] def boundedTensorComparedEvaluation
    (hM : _root_.DerivedCategory.TStructure.t.plus M)
    (e : (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M ⟶
      𝟙_ (Etale.DerivedCategoryModule A Y)) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
      (D(comparisonUpperStar (ModuleCat.{u + 1} A) X).obj M) ⟶
        𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A))) :=
  (compactSupportSiteComparison A c).hom.app ⟨M, hM⟩ ≫
    D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).map e ≫
    (DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso A Y).hom

/-- Transport the specified bounded-origin Hom-chain along a given source identification.
The identification is supplied by the canonical tensor/pullback comparison in every use below.
Source: Stacks Tag 0B65, source naturality
(blueprint: lem-pur-bounded-site-tensor-transposes). -/
@[irreducible] def boundedTensorOriginTranspose
    (J : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (V : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (h : D(comparisonUpperStar (ModuleCat.{u + 1} A) X).obj J.obj ≅ V)
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (z : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj V ⟶ L) :
    V ⟶ D(comparisonUpperStar (ModuleCat.{u + 1} A) X).obj
      (H.obj (R(comparisonLowerStar (ModuleCat.{u + 1} A) Y).obj L)) :=
  h.inv ≫ boundedSiteTranspose A c H adj J L
    ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map h.hom ≫ z)

/-- Canonical source identification with both tensor factors reversed. The braidings
are the existing K-flat derived braidings, including the Koszul signs.
Source: blueprint proof Step 4
(blueprint: lem-pur-bounded-site-tensor-transposes). -/
@[irreducible] def boundedTensorReverseComparison :
    D(comparisonUpperStar (ModuleCat.{u + 1} A) X).obj
      (L(Etale.upperStar (ModuleCat.{u + 1} A) f).obj K ⊗ M) ≅
    L(upperStar (ModuleCat.{u + 1} A) f).obj
      (D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).obj K) ⊗
        D(comparisonUpperStar (ModuleCat.{u + 1} A) X).obj M :=
  D(comparisonUpperStar (ModuleCat.{u + 1} A) X).mapIso
    ((Etale.derivedBraidedCategory (ModuleCat.{u + 1} A) X).braiding
      (L(Etale.upperStar (ModuleCat.{u + 1} A) f).obj K) M) ≪≫
    (projectionComparisonTargetIso A f M K).symm ≪≫
    ((_root_.DerivedCategory.braidedCategory'
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))).braiding
        (D(comparisonUpperStar (ModuleCat.{u + 1} A) X).obj M)
        (L(upperStar (ModuleCat.{u + 1} A) f).obj
          (D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).obj K)))

/-- The transported exceptional counit on a bounded etale-origin dualizing object.
This is B inverse followed by comparison of the etale counit and the site counit.
Source: Stacks Tag 0B65, inverse bounded Hom-chain
(blueprint: lem-pur-bounded-site-tensor-transposes). -/
@[irreducible] def boundedTensorExceptionalCounit
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (hHL : _root_.DerivedCategory.TStructure.t.plus
      (H.obj (R(comparisonLowerStar (ModuleCat.{u + 1} A) Y).obj L))) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
      (D(comparisonUpperStar (ModuleCat.{u + 1} A) X).obj
        (H.obj (R(comparisonLowerStar (ModuleCat.{u + 1} A) Y).obj L))) ⟶ L :=
  (compactSupportSiteComparison A c).hom.app ⟨_, hHL⟩ ≫
    D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).map
      (adj.counit.app (R(comparisonLowerStar (ModuleCat.{u + 1} A) Y).obj L)) ≫
    (derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).counit.app L

/-- The coefficient-normalized rho on the dualizing factor.
Source: blueprint proof Step 5 and the canonical comparison of coefficient units
(blueprint: lem-pur-bounded-site-tensor-transposes). -/
@[irreducible] def boundedTensorDualizingRho :
    D(comparisonUpperStar (ModuleCat.{u + 1} A) X).obj
      (H.obj (𝟙_ (Etale.DerivedCategoryModule A Y))) ⟶
    D(comparisonUpperStar (ModuleCat.{u + 1} A) X).obj
      (H.obj (R(comparisonLowerStar (ModuleCat.{u + 1} A) Y).obj (𝟙_ _))) :=
  boundedSiteRho A H (𝟙_ _) ≫
    D(comparisonUpperStar (ModuleCat.{u + 1} A) X).map
      (H.map (R(comparisonLowerStar (ModuleCat.{u + 1} A) Y).map
        (DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso A Y).hom))

end Arrows

section TensorCompatibility
variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
variable (H : Etale.DerivedCategoryModule A Y ⥤ Etale.DerivedCategoryModule A X)
variable (adj : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ H)

private theorem comparison_reverse_cancel
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {x y : C} {v w : D} (e : x ≅ y) (h : F.obj y ≅ v)
    (s : v ≅ w) (r : w ⟶ v) (hs : s.hom ≫ r = 𝟙 v) :
    (F.mapIso e ≪≫ h ≪≫ s).hom ≫ r = F.map e.hom ≫ h.hom := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc, hs, Category.comp_id]

private theorem transpose_reverse_transport
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) (G : D ⥤ E) {x y : C} {v w z : D} {l : E}
    (tx : (G.obj (F.obj x) ⟶ l) → (F.obj x ⟶ z))
    (ty : (G.obj (F.obj y) ⟶ l) → (F.obj y ⟶ z))
    (e : y ≅ x) (h : F.obj x ≅ v) (b : v ≅ w) (r : w ⟶ v)
    (hb : b.hom ≫ r = 𝟙 v) (q : G.obj v ⟶ l) (u : F.obj x ⟶ z)
    (ht : tx (G.map h.hom ≫ q) = u)
    (hn : ty (G.map (F.map e.hom) ≫ G.map h.hom ≫ q) =
      F.map e.hom ≫ tx (G.map h.hom ≫ q)) :
    ty (G.map ((F.mapIso e ≪≫ h ≪≫ b).hom ≫ r) ≫ q) = F.map e.hom ≫ u := by
  rw [comparison_reverse_cancel F e h b r hb, G.map_comp, Category.assoc]
  exact hn.trans (congrArg (F.map e.hom ≫ ·) ht)

private theorem tensor_evaluation_comparison
    (M : Etale.DerivedCategoryModule A X) (K : Etale.DerivedCategoryModule A Y)
    (hM : _root_.DerivedCategory.TStructure.t.plus M)
    (e : (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M ⟶
      𝟙_ _) :
    ((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A)
      ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M)).hom.app
        K) ≫
      ((derivedTensor (ModuleCat.{u + 1} A) Y).map
        ((compactSupportSiteComparison A c).inv.app ⟨M, hM⟩)).app
          (D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).obj K) ≫
      ((derivedTensor (ModuleCat.{u + 1} A) Y).map
        (boundedTensorComparedEvaluation A c M hM e)).app
          (D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).obj K) ≫
      (λ_ (D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).obj K)).hom =
    D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).map
      (((Etale.derivedTensor (ModuleCat.{u + 1} A) Y).map e).app K ≫ (λ_ K).hom) := by
  have hc : (compactSupportSiteComparison A c).inv.app ⟨M, hM⟩ ≫
      boundedTensorComparedEvaluation A c M hM e =
      D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).map e ≫
        (DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso A Y).hom := by
    unfold boundedTensorComparedEvaluation
    rw [Iso.inv_hom_id_app_assoc]
  have hh := congrArg (fun t ↦ ((derivedTensor (ModuleCat.{u + 1} A) Y).map t).app
    (D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).obj K)) hc
  simp only [Functor.map_comp, NatTrans.comp_app] at hh
  rw [reassoc_of% hh]
  simpa only [Functor.map_comp, NatTrans.comp_app, Category.assoc] using
    siteTensorUnitEvaluation A Y _ K e

private theorem tensor_evaluation_square
    (M : Etale.DerivedCategoryModule A X) (K : Etale.DerivedCategoryModule A Y)
    (hM : _root_.DerivedCategory.TStructure.t.plus M)
    (hJ : _root_.DerivedCategory.TStructure.t.plus
      (M ⊗ L(Etale.upperStar (ModuleCat.{u + 1} A) f).obj K))
    (e : (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M ⟶
      𝟙_ _)
    [IsIso (((Etale.projectionMapOfCompactification
      (ModuleCat.{u + 1} A) c).app M).app K)]
    (ze : (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
      (M ⊗ L(Etale.upperStar (ModuleCat.{u + 1} A) f).obj K) ⟶ K)
    (zp : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
      (D(comparisonUpperStar (ModuleCat.{u + 1} A) X).obj M ⊗
        L(upperStar (ModuleCat.{u + 1} A) f).obj
          (D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).obj K)) ⟶
        D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).obj K)
    (he : ((Etale.projectionMapOfCompactification
      (ModuleCat.{u + 1} A) c).app M).app K ≫ ze =
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) Y).map e).app K ≫ (λ_ K).hom)
    (hp : ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app
      (D(comparisonUpperStar (ModuleCat.{u + 1} A) X).obj M)).app
        (D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).obj K) ≫ zp =
      ((derivedTensor (ModuleCat.{u + 1} A) Y).map
        (boundedTensorComparedEvaluation A c M hM e)).app
          (D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).obj K) ≫
        (λ_ (D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).obj K)).hom) :
    (compactSupportSiteComparison A c).inv.app ⟨_, hJ⟩ ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
        (projectionComparisonTargetIso A f M K).symm.hom ≫ zp =
      D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).map ze := by
  apply (cancel_epi (D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).map
    (((Etale.projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app K))).mp
  have hs := compact_projection_square A c M K hM hJ
  have hs' := congrArg (fun t ↦ t ≫ zp) hs
  dsimp only [derivedTensorRightDerivedLowerShriek,
    rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar,
    Etale.derivedTensorRightDerivedLowerShriek,
    Etale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar,
    Functor.comp_obj, ObjectProperty.ι_obj,
    Functor.whiskeringLeft₂_obj_obj_obj_obj_obj,
    Functor.postcompose₂_obj_obj_obj_obj, Functor.id_obj] at hs' hp ⊢
  simp only [Category.assoc, hp] at hs'
  have hh := hs'.trans (tensor_evaluation_comparison A c M K hM e)
  have hh' := hh.trans (congrArg
    (D(comparisonUpperStar (ModuleCat.{u + 1} A) Y)).map he).symm
  have hh'' := hh'.trans
    ((D(comparisonUpperStar (ModuleCat.{u + 1} A) Y)).map_comp _ _)
  rw [target_comparison_eq]
  simp only [Iso.symm_hom, Iso.symm_inv]
  simp only [Category.assoc, projectionComparisonTensor, Etale.derivedTensor,
    curriedTensor_obj_obj] at hh''
  convert hh'' using 1
  with_unfolding_all rfl

private theorem tensor_projection_naturality
    (M N : Etale.DerivedCategoryModule A X) (K : Etale.DerivedCategoryModule A Y)
    (b : D(comparisonUpperStar (ModuleCat.{u + 1} A) X).obj M ⟶
      D(comparisonUpperStar (ModuleCat.{u + 1} A) X).obj N) :
    ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app
      (D(comparisonUpperStar (ModuleCat.{u + 1} A) X).obj M)).app
        (D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).obj K) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
        (((derivedTensor (ModuleCat.{u + 1} A) X).map b).app
          (L(upperStar (ModuleCat.{u + 1} A) f).obj
            (D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).obj K))) =
    ((derivedTensor (ModuleCat.{u + 1} A) Y).map
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map b)).app
        (D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).obj K) ≫
      ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app
        (D(comparisonUpperStar (ModuleCat.{u + 1} A) X).obj N)).app
          (D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).obj K) := by
  exact (NatTrans.naturality_app
    (projectionMapOfCompactification (ModuleCat.{u + 1} A) c)
    (D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).obj K) b).symm

private theorem tensor_target_naturality
    (M N : Etale.DerivedCategoryModule A X) (K : Etale.DerivedCategoryModule A Y)
    (b : M ⟶ N) :
    D(comparisonUpperStar (ModuleCat.{u + 1} A) X).map
      (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).map b).app
        (L(Etale.upperStar (ModuleCat.{u + 1} A) f).obj K)) ≫
      (projectionComparisonTargetIso A f N K).symm.hom =
    (projectionComparisonTargetIso A f M K).symm.hom ≫
      ((derivedTensor (ModuleCat.{u + 1} A) X).map
        (D(comparisonUpperStar (ModuleCat.{u + 1} A) X).map b)).app
          (L(upperStar (ModuleCat.{u + 1} A) f).obj
            (D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).obj K)) := by
  have ht := NatTrans.naturality_app (comparisonTensorNatIso A X).hom
    (L(Etale.upperStar (ModuleCat.{u + 1} A) f).obj K) b
  simp only [← Iso.app_hom, comparison_tensor_app] at ht
  have hn := ((derivedTensor (ModuleCat.{u + 1} A) X).map
    (D(comparisonUpperStar (ModuleCat.{u + 1} A) X).map b)).naturality
      ((comparisonOpenDerivedPullbackIso A f).hom.app K)
  change D(comparisonUpperStar (ModuleCat.{u + 1} A) X).map
      (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).map b).app
        (L(Etale.upperStar (ModuleCat.{u + 1} A) f).obj K)) ≫
      (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        (ModuleCat.{u + 1} A) N).hom.app
          (L(Etale.upperStar (ModuleCat.{u + 1} A) f).obj K) =
    (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A) M).hom.app
        (L(Etale.upperStar (ModuleCat.{u + 1} A) f).obj K) ≫
      ((derivedTensor (ModuleCat.{u + 1} A) X).map
        (D(comparisonUpperStar (ModuleCat.{u + 1} A) X).map b)).app
          (D(comparisonUpperStar (ModuleCat.{u + 1} A) X).obj
            (L(Etale.upperStar (ModuleCat.{u + 1} A) f).obj K)) at ht
  dsimp only [Functor.comp_obj] at hn
  rw [target_comparison_eq, target_comparison_eq]
  simp only [Iso.symm_hom, Iso.symm_inv, comparisonOpenTensorIso, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ht, Category.assoc, ← hn, ← Category.assoc]

private theorem map_unit_counit
    {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G)
    {x k : C} {l : D} (e : x ⟶ k) (v : F.obj k ⟶ l) :
    F.map e ≫ F.map (a.unit.app k) ≫ a.counit.app (F.obj k) ≫ v =
      F.map e ≫ v := by
  rw [a.left_triangle_components_assoc]

private theorem tensor_counit_comparison
    (hω : _root_.DerivedCategory.TStructure.t.plus
      (H.obj (𝟙_ (Etale.DerivedCategoryModule A Y))))
    (hωp : _root_.DerivedCategory.TStructure.t.plus
      (H.obj (R(comparisonLowerStar (ModuleCat.{u + 1} A) Y).obj (𝟙_ _)))) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
      (boundedTensorDualizingRho A H) ≫
      boundedTensorExceptionalCounit A c H adj (𝟙_ _) hωp =
    boundedTensorComparedEvaluation A c (H.obj (𝟙_ _)) hω
      (adj.counit.app (𝟙_ _)) := by
  let d := H.map ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).unit.app (𝟙_ _)) ≫
    H.map (R(comparisonLowerStar (ModuleCat.{u + 1} A) Y).map
      (DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso A Y).hom)
  have hb := (compactSupportSiteComparison A c).hom.naturality
    (ObjectProperty.homMk d : (⟨_, hω⟩ : DerivedCategory.Plus _) ⟶ ⟨_, hωp⟩)
  have hc := adj.counit.naturality
    ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).unit.app (𝟙_ _) ≫
      R(comparisonLowerStar (ModuleCat.{u + 1} A) Y).map
        (DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso A Y).hom)
  have hu := (derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).counit.naturality
    (DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso A Y).hom
  unfold boundedTensorDualizingRho boundedSiteRho boundedTensorExceptionalCounit
    boundedTensorComparedEvaluation
  rw [← Functor.map_comp]
  change (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
    (D(comparisonUpperStar (ModuleCat.{u + 1} A) X).map d) ≫ _ = _
  change (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
      (D(comparisonUpperStar (ModuleCat.{u + 1} A) X).map d) ≫
      (compactSupportSiteComparison A c).hom.app ⟨_, hωp⟩ =
    (compactSupportSiteComparison A c).hom.app ⟨_, hω⟩ ≫
      D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).map
        ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map d)
      at hb
  rw [← Category.assoc, hb]
  simp only [Category.assoc]
  change (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
      (H.map ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).unit.app (𝟙_ _) ≫
        R(comparisonLowerStar (ModuleCat.{u + 1} A) Y).map
          (DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso A Y).hom)) ≫
      adj.counit.app _ = _ at hc
  dsimp only [Functor.comp_map, Functor.id_obj, Functor.id_map] at hu
  dsimp only [d]
  rw [← H.map_comp]
  erw [← Functor.map_comp_assoc, hc]
  simp only [Functor.map_comp, Functor.id_map, Functor.id_obj, Category.assoc]
  rw [hu]
  exact congrArg (fun z ↦ (compactSupportSiteComparison A c).hom.app ⟨_, hω⟩ ≫ z)
    (map_unit_counit (derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y)
      (adj.counit.app (𝟙_ _))
      (DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso A Y).hom)

end TensorCompatibility

/-- Comparison of the arbitrary tensor evaluation transposes, and the same equality
with both tensor factors reversed by the canonical derived symmetry.
Source: current blueprint lem-pur-co-smooth-etale-locality, proof Steps 1 and 3;
Stacks Tag 0B65 (blueprint: lem-pur-bounded-site-tensor-transposes).

The arrows ze,zp are uniquely prescribed by the forward-projection equations below.
Because the two projection components are isomorphisms, these equations are equivalent
to the inverse-projection composites in the node; they impose no comparison square.

Proof:
1. The proper counit-mate/open projection square of
lem-pur-projection-comparison-etale-origin, with B the inverse of
compactSupportSiteComparison, gives r C(P_e) = P_p b. Invert only P_e and P_p.
2. The symmetric monoidal comparison preserves tensor evaluation and the left unitor.
Since e_p B_M = C_Y(e), compose the inverse projection square to get
z_p F_p(h) B_J = C_Y(z_e).
3. Expand def-pur-bounded-site-transpose-arrows. Naturality of the comparison unit
and of the etale adjunction gives u_p h = C_X(u_e) rho_K. All intermediate etale
objects lie in D+ by the displayed domain assumptions; no unbounded pro-etale
exceptional Hom equivalence is used.
4. Monoidal comparison preserves the derived symmetry. Precompose Step 3 with
C_X of that symmetry to obtain the reversed equation, with its Koszul signs.
5. At M = H(A_Y), e = epsilon_A, the same Hom-chain sends e_p to rho_A.
Consequently it is the actual counit after F_p(rho_A). Projection naturality
identifies the specialized maps with theta of def-pur-co-smoothness.
6. Every map in these composites is natural in M,K,e; inverses of the two natural
projection isomorphisms are natural on precisely this finite-Tor domain. -/
theorem boundedSiteTensorTransposes
    (P : WeilConjectures.PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (_hf : f ≫ aY = aX) (c : Compactification f)
    (H : Etale.DerivedCategoryModule P.Coefficient Y ⥤
      Etale.DerivedCategoryModule P.Coefficient X)
    (adj : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) c ⊣ H)
    (M : Etale.DerivedCategoryModule P.Coefficient X)
    (K : Etale.DerivedCategoryModule P.Coefficient Y)
    (_hMc : Etale.DerivedCategory.isBoundedConstructible P.Coefficient X M)
    (_hKc : WeilConjectures.finiteTorConstructibleEtale P.coefficients.l P.extension
      P.level P.level_pos Y K)
    (hM : _root_.DerivedCategory.TStructure.t.plus M)
    (_hK : _root_.DerivedCategory.TStructure.t.plus K)
    (_hHK : _root_.DerivedCategory.TStructure.t.plus (H.obj K))
    (_hHUK : _root_.DerivedCategory.TStructure.t.plus
      (H.obj (R(comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) Y).obj
        (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj K))))
    (hJ : _root_.DerivedCategory.TStructure.t.plus
      (M ⊗ L(Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj K))
    (hJrev : _root_.DerivedCategory.TStructure.t.plus
      (L(Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj K ⊗ M))
    (e : (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) c).obj M ⟶
        𝟙_ (Etale.DerivedCategoryModule P.Coefficient Y))
    [IsIso (((Etale.projectionMapOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) c).app M).app K)]
    [IsIso (((projectionMapOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).app
      (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).obj M)).app
      (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj K))]
    (ze : (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) c).obj
        (M ⊗ L(Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj K) ⟶ K)
    (zp : (rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) c).obj
        (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).obj M ⊗
          L(upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj
            (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj K)) ⟶
        D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj K)
    (_hze : ((Etale.projectionMapOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) c).app M).app K ≫ ze =
        ((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).map e).app K ≫
          (λ_ K).hom)
    (_hzp : ((projectionMapOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).app
      (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).obj M)).app
      (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj K) ≫ zp =
        ((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).map
          (boundedTensorComparedEvaluation P.Coefficient c M hM e)).app
          (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj K) ≫
        (λ_ (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj K)).hom) :
    boundedSiteTranspose P.Coefficient c H adj ⟨_, hJ⟩
      (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj K)
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).map
        (projectionComparisonTargetIso P.Coefficient f M K).symm.hom ≫ zp) =
      D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).map
        ((adj.homEquiv _ K) ze) ≫ boundedSiteRho P.Coefficient H K ∧
    boundedSiteTranspose P.Coefficient c H adj ⟨_, hJrev⟩
      (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj K)
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).map
        ((boundedTensorReverseComparison P.Coefficient (f := f) M K).hom ≫
          ((_root_.DerivedCategory.braidedCategory'
            (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))).braiding
              (L(upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj
                (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj K))
              (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).obj M)).hom) ≫ zp) =
      D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).map
        (((Etale.derivedBraidedCategory (ModuleCat.{u + 1} P.Coefficient) X).braiding
          (L(Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj K) M).hom ≫
            (adj.homEquiv _ K) ze) ≫ boundedSiteRho P.Coefficient H K := by
  have hs := tensor_evaluation_square P.Coefficient c M K hM hJ e ze zp _hze _hzp
  have ht := boundedSiteTranspose_compatible P.Coefficient c H adj ⟨_, hJ⟩ K ze
    ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).map
      (projectionComparisonTargetIso P.Coefficient f M K).symm.hom ≫ zp) hs
  refine ⟨ht, ?_⟩
  have hsym := _root_.DerivedCategory.braiding_hom_braiding_hom
    (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))
    (fun U V ↦ SymmetricCategory.symmetry U V)
    (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).obj M)
    (L(upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj
      (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj K))
  have hn := boundedSiteTranspose_left P.Coefficient c H adj ⟨_, hJ⟩ ⟨_, hJrev⟩
    (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj K)
    ((Etale.derivedBraidedCategory (ModuleCat.{u + 1} P.Coefficient) X).braiding
      (L(Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj K) M).hom
    ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).map
      (projectionComparisonTargetIso P.Coefficient f M K).symm.hom ≫ zp)
  have hr := transpose_reverse_transport
    D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X)
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient) c)
    (boundedSiteTranspose P.Coefficient c H adj ⟨_, hJ⟩ _)
    (boundedSiteTranspose P.Coefficient c H adj ⟨_, hJrev⟩ _)
    ((Etale.derivedBraidedCategory (ModuleCat.{u + 1} P.Coefficient) X).braiding
      (L(Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj K) M)
    (projectionComparisonTargetIso P.Coefficient f M K).symm
    ((_root_.DerivedCategory.braidedCategory'
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))).braiding
        (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).obj M)
        (L(upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj
          (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj K))) _ hsym
    zp _ ht hn
  unfold boundedTensorReverseComparison
  simp only [Functor.map_comp, Category.assoc] at hr ⊢
  convert hr using 1
  with_unfolding_all rfl

/-- The theta specialization: the pro-etale evaluation is the actual transported
exceptional counit, and the source dualizing factor is changed by the unit-normalized rho.
Tensor symmetry gives the pullback-first theta convention of def-pur-co-smoothness.
The object Jp retains the bounded-below origin used by the transported pro-etale transpose.
Source: current blueprint, lem-pur-co-smooth-etale-locality, proof Step 3
(blueprint: lem-pur-bounded-site-tensor-transposes).

Proof: specialize boundedSiteTensorTransposes to M = H(A_Y) and e = epsilon_A.
The bounded site Hom-chain sends the compared evaluation to rho_A, since the
etale transpose of the counit is the identity. Its inverse therefore identifies
that evaluation with the transported exceptional counit after F_p(rho_A).
Naturality of the compactification projection moves rho_A to the tensor source.
This gives exactly the displayed theta equation. Precompose with the canonical
symmetry to obtain the node's pullback-first theta equation, including Koszul signs.
The coefficient-unit comparison is inserted in boundedTensorDualizingRho.
-/
theorem boundedSiteTensorTransposes_dualizing
    (P : WeilConjectures.PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (_hf : f ≫ aY = aX) (c : Compactification f)
    (H : Etale.DerivedCategoryModule P.Coefficient Y ⥤
      Etale.DerivedCategoryModule P.Coefficient X)
    (adj : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) c ⊣ H)
    (K : Etale.DerivedCategoryModule P.Coefficient Y)
    (_hKc : WeilConjectures.finiteTorConstructibleEtale P.coefficients.l P.extension
      P.level P.level_pos Y K)
    (_hK : _root_.DerivedCategory.TStructure.t.plus K)
    (_hHK : _root_.DerivedCategory.TStructure.t.plus (H.obj K))
    (_hHUK : _root_.DerivedCategory.TStructure.t.plus
      (H.obj (R(comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) Y).obj
        (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj K))))
    (_hωc : Etale.DerivedCategory.isBoundedConstructible P.Coefficient X
      (H.obj (𝟙_ (Etale.DerivedCategoryModule P.Coefficient Y))))
    (_hω : _root_.DerivedCategory.TStructure.t.plus
      (H.obj (𝟙_ (Etale.DerivedCategoryModule P.Coefficient Y))))
    (hωp : _root_.DerivedCategory.TStructure.t.plus
      (H.obj (R(comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) Y).obj (𝟙_ _))))
    (Jp : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)))
    (jp : Jp.obj ≅
      H.obj (R(comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) Y).obj (𝟙_ _)) ⊗
        L(Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj K)
    (ze : (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) c).obj
        (H.obj (𝟙_ (Etale.DerivedCategoryModule P.Coefficient Y)) ⊗
          L(Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj K) ⟶ K)
    (zp : (rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) c).obj
        (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).obj
          (H.obj (R(comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) Y).obj (𝟙_ _))) ⊗
            L(upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj
              (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj K)) ⟶
        D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj K)
    [IsIso (((Etale.projectionMapOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) c).app
        (H.obj (𝟙_ (Etale.DerivedCategoryModule P.Coefficient Y)))).app K)]
    [IsIso (((projectionMapOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).app
      (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).obj
        (H.obj (R(comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) Y).obj
          (𝟙_ _))))).app (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj K))]
    (_hze : ((Etale.projectionMapOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) c).app
        (H.obj (𝟙_ (Etale.DerivedCategoryModule P.Coefficient Y)))).app K ≫ ze =
      ((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).map
        (adj.counit.app (𝟙_ _))).app K ≫ (λ_ K).hom)
    (_hzp : ((projectionMapOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).app
      (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).obj
        (H.obj (R(comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) Y).obj
          (𝟙_ _))))).app (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj K) ≫
        zp = ((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).map
          (boundedTensorExceptionalCounit P.Coefficient c H adj (𝟙_ _) hωp)).app
            (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj K) ≫
          (λ_ (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj K)).hom) :
    (projectionComparisonTargetIso P.Coefficient f
        (H.obj (𝟙_ (Etale.DerivedCategoryModule P.Coefficient Y))) K).symm.hom ≫
      ((derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).map
        (boundedTensorDualizingRho P.Coefficient H)).app
          (L(upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj
            (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj K)) ≫
      boundedTensorOriginTranspose P.Coefficient c H adj Jp _
        (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapIso jp ≪≫
          (projectionComparisonTargetIso P.Coefficient f
            (H.obj (R(comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) Y).obj
              (𝟙_ _))) K).symm)
        (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj K) zp =
      D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).map
        ((adj.homEquiv _ K) ze) ≫ boundedSiteRho P.Coefficient H K := by
  let ω := H.obj (𝟙_ (Etale.DerivedCategoryModule P.Coefficient Y))
  let ωp := H.obj (R(comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) Y).obj (𝟙_ _))
  let d : ω ⟶ ωp := H.map
    ((derivedComparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) Y).unit.app (𝟙_ _) ≫
      R(comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) Y).map
        (DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso P.Coefficient Y).hom)
  let b := ((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).map d).app
    (L(Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj K)
  let w := ((derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).map
    (boundedTensorDualizingRho P.Coefficient H)).app
      (L(upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj
        (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj K))
  have hd : boundedTensorDualizingRho P.Coefficient H =
      D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).map d := by
    unfold boundedTensorDualizingRho boundedSiteRho d
    simp only [Functor.map_comp]
  have hn := tensor_target_naturality P.Coefficient (f := f) ω ωp K d
  rw [← hd] at hn
  have hJ : _root_.DerivedCategory.TStructure.t.plus
      (ω ⊗ L(Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj K) := by
    obtain ⟨a, b, hab, ht⟩ := _hKc.2
    exact plus_tensor_of_tor P.Coefficient f ω K
      (bounded_of_constructible P.Coefficient X ω _hωc) ⟨a, b, ht⟩
  let z0 := (rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} P.Coefficient) c).map w ≫ zp
  have hp0 : ((projectionMapOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).app
      (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).obj ω)).app
        (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj K) ≫ z0 =
      ((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).map
        (boundedTensorComparedEvaluation P.Coefficient c ω _hω
          (adj.counit.app (𝟙_ _)))).app
            (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj K) ≫
        (λ_ (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj K)).hom := by
    dsimp only [z0, rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar,
      derivedTensorRightDerivedLowerShriek, Functor.comp_obj,
      Functor.whiskeringLeft₂_obj_obj_obj_obj_obj, Functor.postcompose₂_obj_obj_obj_obj]
    have hn := tensor_projection_naturality P.Coefficient c ω ωp K
      (boundedTensorDualizingRho P.Coefficient H)
    dsimp only [rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar,
      derivedTensorRightDerivedLowerShriek, Functor.comp_obj,
      Functor.whiskeringLeft₂_obj_obj_obj_obj_obj, Functor.postcompose₂_obj_obj_obj_obj] at hn
    erw [← Category.assoc, hn, Category.assoc, _hzp]
    simp only [← Category.assoc]
    rw [← NatTrans.comp_app, ← Functor.map_comp, tensor_counit_comparison]
  have hs := tensor_evaluation_square P.Coefficient c ω K _hω hJ
    (adj.counit.app (𝟙_ _)) ze z0 _hze hp0
  have ht := boundedSiteTranspose_compatible P.Coefficient c H adj ⟨_, hJ⟩ K ze
    ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).map
      (projectionComparisonTargetIso P.Coefficient f ω K).symm.hom ≫ z0) hs
  let h := D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapIso jp ≪≫
    (projectionComparisonTargetIso P.Coefficient f ωp K).symm
  have hsource :
      (projectionComparisonTargetIso P.Coefficient f ω K).symm.hom ≫ w ≫ h.inv =
        D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).map (b ≫ jp.inv) := by
    dsimp only [h, Iso.trans_inv, Functor.mapIso_inv]
    rw [← Category.assoc, ← hn]
    simp only [Iso.symm_hom, Iso.symm_inv, Category.assoc, Iso.inv_hom_id_assoc,
      ← Functor.map_comp]
    rfl
  unfold boundedTensorOriginTranspose
  change (projectionComparisonTargetIso P.Coefficient f ω K).symm.hom ≫ w ≫
    (h.inv ≫ boundedSiteTranspose P.Coefficient c H adj Jp _
      ((rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} P.Coefficient) c).map h.hom ≫ zp)) = _
  rw [← Category.assoc w h.inv, ← Category.assoc _ (w ≫ h.inv), hsource,
    ← boundedSiteTranspose_left P.Coefficient c H adj Jp ⟨_, hJ⟩]
  simp only [← Category.assoc, ← Functor.map_comp]
  have hmap : D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).map
      (b ≫ jp.inv) ≫ h.hom =
      (projectionComparisonTargetIso P.Coefficient f ω K).symm.hom ≫ w := by
    have hh := congrArg (fun z ↦ z ≫ h.hom) hsource
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hh.symm
  rw [hmap]
  simpa only [z0, Functor.map_comp, Category.assoc] using ht

/-- Source and target naturality of the two transpose functions used above.
Tensor functoriality, projection naturality and the unitor identify compatible
changes of M,K,e with the b,v pre- and postcompositions in this formula.
Source: Stacks Tag 0B65; node proof Steps 3 and 5
(blueprint: lem-pur-bounded-site-tensor-transposes).

Proof: expand boundedSiteTranspose. Naturality of B moves F_p(C_X(b)) to
C_Y(F_e(b)). Apply source and target naturality successively to the comparison
adjunction and the etale adjunction, and use functoriality of C_X. The second
identity is exactly source and target naturality of the etale adjunction.
All origins J,J' are in D+; no exceptional adjunction on arbitrary pro-etale
objects is used. Substitution of the normalized projection/evaluation composites
gives naturality of both comparison identities in M,K,e. -/
theorem boundedSiteTensorTransposes_natural
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (H : Etale.DerivedCategoryModule A Y ⥤ Etale.DerivedCategoryModule A X)
    (adj : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ H)
    (J J' : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (K K' : Etale.DerivedCategoryModule A Y) (b : J'.obj ⟶ J.obj) (v : K ⟶ K')
    (ze : (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) c).obj J.obj ⟶ K)
    (zp : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
      (D(comparisonUpperStar (ModuleCat.{u + 1} A) X).obj J.obj) ⟶
        D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).obj K) :
    boundedSiteTranspose A c H adj J'
      (D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).obj K')
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
        (D(comparisonUpperStar (ModuleCat.{u + 1} A) X).map b) ≫ zp ≫
          D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).map v) =
      D(comparisonUpperStar (ModuleCat.{u + 1} A) X).map b ≫
        boundedSiteTranspose A c H adj J
          (D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).obj K) zp ≫
        D(comparisonUpperStar (ModuleCat.{u + 1} A) X).map
          (H.map (R(comparisonLowerStar (ModuleCat.{u + 1} A) Y).map
            (D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).map v))) ∧
    (adj.homEquiv J'.obj K')
      ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map b ≫
        ze ≫ v) = b ≫ (adj.homEquiv J.obj K) ze ≫ H.map v  := by
  constructor
  · rw [boundedSiteTranspose_left, boundedSiteTranspose_right]
  · rw [Adjunction.homEquiv_naturality_left,
      Adjunction.homEquiv_naturality_right]


end AlgebraicGeometry.ProEtale
