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

omit [Finite k₀] [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))] [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
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
      Functor.isoWhiskerLeft (upperStar g) (geometricFiberBoundedConstructibleFunctorCompιIso k₀ l Z) ≪≫
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

/-- The components of `AlgebraicGeometry.WeilComplex.geometricFiberBoundedConstructibleFunctorUpperStarIso`
on the ambient derived categories. -/
lemma ι_map_geometricFiberBoundedConstructibleFunctorUpperStarIso_hom_app (T : WeilComplex k₀ l Y) :
    (ObjectProperty.ι _).map ((geometricFiberBoundedConstructibleFunctorUpperStarIso g).hom.app T) =
      (Functor.mapDerivedCategoryCompIso (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z))
          (adicSheafEquivCondensedMod l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor).inv.app
          ((ProEtaleWeilSheaf.upperStar k₀ l g).mapDerivedCategory.obj T.obj) ≫
        (ProEtaleWeilSheaf.derivedCondensedRealizationUpperStarIso k₀ l g).inv.app T.obj ≫
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (Scheme.Hom.geometricFiberMap g
            (comp_over g (Spec (CommRingCat.of k₀))))).leftDerivedFunctor.map
          ((Functor.mapDerivedCategoryCompIso (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Y))
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

end AlgebraicGeometry.WeilComplex
