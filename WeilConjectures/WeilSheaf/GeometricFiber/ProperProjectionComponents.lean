/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.GeometricFiber.ProperLowerStar
public import WeilConjectures.WeilSheaf.Native.Projection.ProperProjectionIso
public import WeilConjectures.PoincareDuality.ProjectionFormulaOpenImmersion
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMorphismDualizable

/-!
# The comparisons entering the proper projection formula of forgetful functors

For a morphism `g : Z ⟶ Y` of separated `k₀`-schemes of finite type with base change `ḡ` to the
geometric fibres, we record the comparisons of forgetting the Weil structure
(`For`, `AlgebraicGeometry.WeilComplex.geometricFiberBoundedConstructibleFunctor`) with the
pullbacks (`AlgebraicGeometry.WeilComplex.geometricFiberBoundedConstructibleFunctorUpperStarIso`)
and, for `g` proper, the proper projection formula of Weil complexes
(`AlgebraicGeometry.WeilComplex.derivedLowerStarNativeConstructibleTensorIso`), together with
the components on the ambient derived categories of these comparisons and of the comparisons with
the tensor products and the direct images.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Endofunctor

namespace AlgebraicGeometry.WeilComplex

open ProEtale

attribute [local implicit_reducible] AlgebraicGeometry.instCategoryWeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]

omit [Finite k₀] [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] in
/-- The underlying morphism of `geometricFiberHom g` is the base change of `g`. -/
lemma geometricFiberHom_left :
    (geometricFiberHom (k₀ := k₀) g).left =
      Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))) :=
  rfl

/-- The objects underlying the images of Weil complexes under a functor between full
subcategories induced by a functor of the ambient categories. -/
lemma liftFullSubcategory_obj_obj_weilComplex {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    {D : Type*} [Category D] (Q : ObjectProperty D)
    (F : DerivedCategory (ProEtaleWeilSheaf k₀ l X) ⥤ D)
    (h : ∀ K, objectProperty k₀ l X K → Q (F.obj K)) (T : WeilComplex k₀ l X) :
    (((objectProperty k₀ l X).liftFullSubcategory Q F h).obj T).obj = F.obj T.obj :=
  rfl

/-- **Forgetting the Weil structure commutes with pullback**: `For ∘ g^* ≅ ḡ^* ∘ For`, the
comparison `AlgebraicGeometry.ProEtaleWeilSheaf.derivedCondensedRealizationUpperStarIso` of the
derived condensed realization with the pullbacks, restricted to Weil complexes. -/
noncomputable def geometricFiberBoundedConstructibleFunctorUpperStarIso :
    upperStar g ⋙ geometricFiberBoundedConstructibleFunctor k₀ l Z ≅
      geometricFiberBoundedConstructibleFunctor k₀ l Y ⋙
        CondensedRing.boundedConstructibleUpperStar _ l (geometricFiberHom (k₀ := k₀) g) :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (upperStar g)
        (geometricFiberBoundedConstructibleFunctorCompιIso k₀ l Z) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        ((objectProperty k₀ l Y).liftFullSubcategoryCompιIso (objectProperty k₀ l Z)
          (ProEtaleWeilSheaf.upperStar k₀ l g).mapDerivedCategory _) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (objectProperty k₀ l Y).ι
        (ProEtaleWeilSheaf.derivedCondensedRealizationUpperStarIso k₀ l g).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (geometricFiberBoundedConstructibleFunctorCompιIso k₀ l Y).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (geometricFiberBoundedConstructibleFunctor k₀ l Y)
        (CondensedRing.boundedConstructibleUpperStarCompatibility _ l
          (geometricFiberHom (k₀ := k₀) g)).symm ≪≫
      (Functor.associator _ _ _).symm)

/-- The components of the pullback comparison of forgetting the Weil structure
(`AlgebraicGeometry.WeilComplex.geometricFiberBoundedConstructibleFunctorUpperStarIso`) on the
ambient derived categories. -/
lemma ι_map_geometricFiberBoundedConstructibleFunctorUpperStarIso_hom_app (T : WeilComplex k₀ l Y) :
    (ObjectProperty.ι _).map ((geometricFiberBoundedConstructibleFunctorUpperStarIso g).hom.app T) =
      (Functor.mapDerivedCategoryCompIso (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z))
          (adicSheafEquivCondensedMod l
            (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor).inv.app
          ((ProEtaleWeilSheaf.upperStar k₀ l g).mapDerivedCategory.obj T.obj) ≫
        (ProEtaleWeilSheaf.derivedCondensedRealizationUpperStarIso k₀ l g).inv.app T.obj ≫
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (Scheme.Hom.geometricFiberMap g
            (comp_over g (Spec (CommRingCat.of k₀))))).leftDerivedFunctor.map
          ((Functor.mapDerivedCategoryCompIso
            (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Y))
            (adicSheafEquivCondensedMod l
              (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor).hom.app T.obj) := by
  simp only [geometricFiberBoundedConstructibleFunctorUpperStarIso,
    Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.whiskeringRight_preimage_app,
    ObjectProperty.ι_map, ObjectProperty.homMk_hom, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    geometricFiberBoundedConstructibleFunctorCompιIso, Iso.symm_inv, Functor.isoWhiskerLeft_inv,
    ObjectProperty.liftFullSubcategoryCompιIso, Iso.refl_hom, NatTrans.id_app,
    CondensedRing.boundedConstructibleUpperStarCompatibility, ObjectProperty.liftCompιIso,
    Iso.refl_inv, Category.id_comp, Category.comp_id, CategoryTheory.Functor.map_id]
  dsimp only [Functor.comp_obj, ObjectProperty.ι_obj, ObjectProperty.liftFullSubcategory_obj_obj,
    ObjectProperty.lift_obj_obj, geometricFiberBoundedConstructibleFunctor, WeilComplex.forget,
    upperStar, ProEtaleWeilSheaf.derivedCondensedRealization,
    CondensedRing.boundedConstructibleUpperStar, adicSheafDerivedEquivCondensedMod_functor,
    geometricFiberHom_left, liftFullSubcategory_obj_obj_weilComplex]
  simp only [Category.id_comp, Category.comp_id]
  erw [Category.id_comp]

set_option maxHeartbeats 1000000 in
-- the derived categories of condensed modules are slow to elaborate
set_option synthInstance.maxHeartbeats 400000 in
-- the monoidal structure of the derived category of condensed modules is found slowly
/-- The components of the tensor comparison of forgetting the Weil structure
(`AlgebraicGeometry.WeilComplex.geometricFiberBoundedConstructibleFunctorTensorIso`) on the
ambient derived categories. -/
lemma ι_map_geometricFiberBoundedConstructibleFunctorTensorIso_hom_app (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))] [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] (A B : WeilComplex k₀ l X) :
    (ObjectProperty.ι _).map
      ((geometricFiberBoundedConstructibleFunctorTensorIso k₀ l X).hom.app (A, B)) =
      (Functor.mapDerivedCategoryCompIso (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X))
          (adicSheafEquivCondensedMod l
            (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor).inv.app
          ((ProEtaleWeilSheaf.nativeDerivedTensor k₀ l X).obj (A.obj, B.obj)) ≫
        (ProEtaleWeilSheaf.condensedRealizationTensor k₀ l X).hom.app (A.obj, B.obj) ≫
        (Functor.mapDerivedCategoryCompIso (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X))
          (adicSheafEquivCondensedMod l
            (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor).hom.app A.obj ▷ _ ≫
        _ ◁ (Functor.mapDerivedCategoryCompIso
          (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X))
          (adicSheafEquivCondensedMod l
            (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor).hom.app B.obj := by
  simp only [geometricFiberBoundedConstructibleFunctorTensorIso,
    Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.whiskeringRight_preimage_app,
    ObjectProperty.ι_map, ObjectProperty.homMk_hom, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    geometricFiberBoundedConstructibleFunctorCompιIso, Iso.symm_inv, Functor.isoWhiskerLeft_inv,
    Iso.refl_hom, NatTrans.id_app, Iso.refl_inv, Category.id_comp, Category.comp_id,
    CategoryTheory.Functor.map_id, boundedConstructibleιTensorIso, NatIso.ofComponents_hom_app,
    NatIso.prod_hom, Functor.prod_map, NatTrans.prod_app_fst, NatTrans.prod_app_snd,
    curriedTensor_map_app, curriedTensor_obj_map]
  dsimp only [Functor.comp_obj, ObjectProperty.ι_obj, ObjectProperty.lift_obj_obj,
    geometricFiberBoundedConstructibleFunctor, WeilComplex.forget, nativeConstructibleTensor,
    ProEtaleWeilSheaf.derivedCondensedRealization, adicSheafDerivedEquivCondensedMod_functor,
    Functor.prod_obj, Functor.uncurry_obj_obj, Functor.uncurry_obj_map]
  erw [NatTrans.prod_app_fst, NatTrans.prod_app_snd]
  simp only [Functor.whiskerLeft_app, curriedTensor_map_app, curriedTensor_obj_map,
    Category.id_comp, Category.comp_id, ObjectProperty.ι_obj]
  erw [Category.id_comp, Category.comp_id]

variable [IsProper g]

/-- **The proper projection formula of Weil complexes**: `Rg_* A ⊗ T ≅ Rg_*(A ⊗ g^* T)`, the
canonical projection isomorphism
`AlgebraicGeometry.WeilComplex.rightDerivedLowerStarNativeDerivedTensorIso` restricted to Weil
complexes. -/
noncomputable def derivedLowerStarNativeConstructibleTensorIso :
    (derivedLowerStar g).prod (𝟭 _) ⋙ nativeConstructibleTensor k₀ l Y ≅
      (𝟭 _).prod (upperStar g) ⋙ nativeConstructibleTensor k₀ l Z ⋙ derivedLowerStar g :=
  ((objectProperty k₀ l Y).fullyFaithfulι.whiskeringRight _).preimageIso
    (rightDerivedLowerStarNativeDerivedTensorIso g)

set_option maxHeartbeats 1000000 in
-- the derived categories of the three models are slow to elaborate
/-- The components of the inverse of
`AlgebraicGeometry.WeilComplex.geometricFiberBoundedConstructibleFunctorLowerStarIso` on the
ambient derived categories: the derived base change map of the condensed realization, up to the
identifications `D(forget ⋙ Φ) ≅ D(forget) ⋙ D(Φ)`. -/
lemma ι_map_geometricFiberBoundedConstructibleFunctorLowerStarIso_inv_app
    (M : WeilComplex k₀ l Z) :
    (ObjectProperty.ι _).map ((geometricFiberBoundedConstructibleFunctorLowerStarIso g).inv.app M) =
      (Functor.mapDerivedCategoryCompIso (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Y))
          (adicSheafEquivCondensedMod l
            (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor).inv.app
          ((ProEtaleWeilSheaf.lowerStar k₀ l g).rightDerivedFunctor.obj M.obj) ≫
        (mateEquiv (ProEtaleWeilSheaf.derivedUpperStarLowerStarAdjunction k₀ l g)
          (CondensedRing.derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l)
            (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
          (ProEtaleWeilSheaf.derivedCondensedRealizationUpperStarIso k₀ l g).hom).natTrans.app
          M.obj ≫
        (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
            (Scheme.Hom.geometricFiberMap g
              (comp_over g (Spec (CommRingCat.of k₀))))).rightDerivedFunctor.map
          ((Functor.mapDerivedCategoryCompIso
            (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z))
            (adicSheafEquivCondensedMod l
              (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor).hom.app M.obj) := by
  simp only [geometricFiberBoundedConstructibleFunctorLowerStarIso,
    Functor.FullyFaithful.preimageIso_inv, Functor.FullyFaithful.whiskeringRight_preimage_app,
    ObjectProperty.ι_map, ObjectProperty.homMk_hom, Iso.trans_inv, NatTrans.comp_app,
    Iso.symm_inv, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, geometricFiberBoundedConstructibleFunctorCompιIso,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom, ObjectProperty.liftFullSubcategoryCompιIso,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    CondensedRing.boundedConstructibleLowerStarCompatibility, ObjectProperty.liftCompιIso,
    asIso_hom, Category.id_comp, Category.comp_id, CategoryTheory.Functor.map_id]
  dsimp only [Functor.comp_obj, ObjectProperty.ι_obj, ObjectProperty.lift_obj_obj,
    geometricFiberBoundedConstructibleFunctor, WeilComplex.forget, derivedLowerStar,
    ProEtaleWeilSheaf.derivedCondensedRealization, adicSheafDerivedEquivCondensedMod_functor,
    CondensedRing.boundedConstructibleLowerStar, geometricFiberHom_left,
    liftFullSubcategory_obj_obj_weilComplex]
  simp only [Category.id_comp, Category.comp_id, CategoryTheory.Functor.map_id]
  erw [Category.id_comp]
  simp only [Category.assoc]

/-- The components of the proper projection formula of Weil complexes on the ambient derived
categories are the canonical projection maps. -/
lemma ι_map_derivedLowerStarNativeConstructibleTensorIso_hom_app (A : WeilComplex k₀ l Z)
    (T : WeilComplex k₀ l Y) :
    ((derivedLowerStarNativeConstructibleTensorIso g).hom.app (A, T)).hom =
      (((ProEtaleWeilSheaf.derivedUpperStarLowerStarAdjunction k₀ l g).rightAdjointProjectionMap
        (ProEtaleWeilSheaf.nativeCurriedPullTensor k₀ l g)).app A.obj).app T.obj := by
  simp only [derivedLowerStarNativeConstructibleTensorIso, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.whiskeringRight_preimage_app, ObjectProperty.ι_map,
    ObjectProperty.homMk_hom]
  rfl

set_option synthInstance.maxHeartbeats 400000 in
-- the monoidal structure of the derived category of condensed modules is found slowly
omit [Finite k₀] [Fact (ringChar k₀ ≠ l)] in
/-- The comonoidal structure of the derived pullback `Lf^*` of condensed `ℚ̄_ℓ`-modules is the
comparison `Lf^*(a ⊗ b) ⟶ Lf^* a ⊗ Lf^* b`. -/
lemma δNatTrans_leftDerivedUpperStar {X₀ Y₀ : Scheme.{u}} (f : X₀ ⟶ Y₀) :
    Functor.OplaxMonoidal.δNatTrans
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).leftDerivedFunctor =
      CondensedRing.leftDerivedUpperStarTensor (Profinite.padicAlgClRingObj l) f := by
  ext K L
  rfl

set_option synthInstance.maxHeartbeats 400000 in
-- the monoidal structure of the derived category of condensed modules is found slowly
omit [Finite k₀] [Fact (ringChar k₀ ≠ l)] in
/-- The right adjoint projection map of `Lf^* ⊣ Rf_*` for the comparison
`Lf^*(a ⊗ b) ⟶ Lf^* a ⊗ Lf^* b` is the projection morphism of the monoidal functor `Lf^*`. -/
lemma rightAdjointProjectionMap_leftDerivedUpperStarTensor_app_app {X₀ Y₀ : Scheme.{u}}
    (f : X₀ ⟶ Y₀) (A B) :
    (((CondensedRing.derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l)
        f).rightAdjointProjectionMap
          (CondensedRing.leftDerivedUpperStarTensor (Profinite.padicAlgClRingObj l) f)).app A).app
        B =
      (CondensedRing.derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l)
        f).projectionMorphism A B := by
  rw [Adjunction.projectionMorphism_eq_rightAdjointProjectionMap, δNatTrans_leftDerivedUpperStar]

/-- On the ambient derived categories, forgetting the Weil structure acts on morphisms by the
forgetful functor followed by the comparison of the two models. -/
lemma ι_map_geometricFiberBoundedConstructibleFunctor_map (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))] [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] {A B : WeilComplex k₀ l X} (φ : A ⟶ B) :
    (ObjectProperty.ι _).map ((geometricFiberBoundedConstructibleFunctor k₀ l X).map φ) =
      (adicSheafEquivCondensedMod l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.mapDerivedCategory.map
        ((IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategory.map φ.hom) :=
  rfl

set_option synthInstance.maxHeartbeats 400000 in
-- the monoidal structure of the derived category of condensed modules is found slowly
open scoped CategoryTheory.Obj in
/-- The inclusion of bounded constructible complexes into the derived category commutes with
right whiskering. -/
lemma boundedConstructible_ι_map_whiskerRight (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))] [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    {M N : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l)
      (Over.mk (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure).left)}
    (φ : M ⟶ N) (A : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l)
      (Over.mk (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure).left)) :
    (ObjectProperty.ι _).map (φ ▷ A) = (ObjectProperty.ι _).map φ ▷ A.obj :=
  rfl

set_option synthInstance.maxHeartbeats 400000 in
-- the monoidal structure of the derived category of condensed modules is found slowly
open scoped CategoryTheory.Obj in
/-- The inclusion of bounded constructible complexes into the derived category commutes with
left whiskering. -/
lemma boundedConstructible_ι_map_whiskerLeft' (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))] [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    (A : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l)
      (Over.mk (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure).left))
    {M N : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l)
      (Over.mk (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure).left)}
    (φ : M ⟶ N) :
    (ObjectProperty.ι _).map (A ◁ φ) = A.obj ◁ (ObjectProperty.ι _).map φ :=
  rfl

/-- On the ambient derived categories, the direct image `Rḡ_*` of bounded constructible
complexes acts on morphisms as that of the derived categories. -/
lemma ι_map_boundedConstructibleLowerStar_geometricFiberHom_map {M M'} (φ : M ⟶ M') :
    (ObjectProperty.ι _).map
      ((CondensedRing.boundedConstructibleLowerStar l (geometricFiberHom (k₀ := k₀) g)).map φ) =
      (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
        (Scheme.Hom.geometricFiberMap g
          (comp_over g (Spec (CommRingCat.of k₀))))).rightDerivedFunctor.map
        ((ObjectProperty.ι _).map φ) :=
  rfl

set_option synthInstance.maxHeartbeats 400000 in
-- the monoidal structure of the derived category of condensed modules is found slowly
/-- The projection morphism of `Lḡ^* ⊣ Rḡ_*` on bounded constructible complexes is that of the
ambient derived categories. -/
lemma ι_map_boundedConstructibleProjectionMorphism_geometricFiberHom (M N) :
    (ObjectProperty.ι _).map
      ((CondensedRing.boundedConstructibleUpperStarLowerStarAdjunction l
        (geometricFiberHom (k₀ := k₀) g)).projectionMorphism M N) =
      (CondensedRing.derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l)
        (geometricFiberHom (k₀ := k₀) g).left).projectionMorphism M.obj N.obj :=
  CondensedRing.boundedConstructibleProjectionMorphism_hom l _ M N

end AlgebraicGeometry.WeilComplex
