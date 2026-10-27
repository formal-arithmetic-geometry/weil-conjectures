/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory

/-!
# Left derived functors: invariance under isomorphism and postcomposition with exact functors

Let `C` be a monoidal abelian category with functorial flat resolutions, so that additive
functors `G : C ⥤ D` preserving quasi-isomorphisms between K-flat complexes have a total left
derived functor `L(G)` computed on K-flat resolutions
(`WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs`). This file proves two
formal compatibilities, without any exactness assumption on `G`:

- `Functor.leftDerivedFunctorIsoOfIso`: an isomorphism `G ≅ G'` induces an isomorphism
  `L(G) ≅ L(G')` (for exact functors this is `Functor.leftDerivedFunctorNatIso`);
- `Functor.leftDerivedFunctorCompMapDerivedCategoryRightIso`: for an exact functor `F'`, the
  left derived functor of `G ⋙ F'` is `L(G) ⋙ D(F')`. Indeed `L(G)` is computed on a K-flat
  complex `K` by `G K`, and `F'` is applied levelwise. This is the counterpart, with the exact
  functor on the other side, of `Functor.leftDerivedFunctorCompMapDerivedCategoryIso`, and it
  needs no hypothesis on K-flat complexes.

-/

@[expose] public section

universe wC wD wE vC vD vE uC uD uE

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.Functor

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]

section Iso

variable {G G' : C ⥤ D} [G.Additive] [G'.Additive] [G.PreservesKFlatQuasiIso]
  [G'.PreservesKFlatQuasiIso]

/-- An isomorphism `G ≅ G'` of additive functors preserving K-flat quasi-isomorphisms induces
an isomorphism `L(G) ≅ L(G')` of their total left derived functors. -/
noncomputable def leftDerivedFunctorIsoOfIso (e : G ≅ G') :
    G.leftDerivedFunctor ≅ G'.leftDerivedFunctor :=
  leftDerivedNatIso G.leftDerivedFunctor G'.leftDerivedFunctor G.leftDerivedFunctorCounit
    G'.leftDerivedFunctorCounit (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
    (isoWhiskerRight (NatIso.mapHomotopyCategory e (ComplexShape.up ℤ)) DerivedCategory.Qh)

end Iso

section CompRight

variable {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]
  (G : C ⥤ D) [G.Additive] [G.PreservesKFlatQuasiIso]
  (F' : D ⥤ E) [F'.Additive] [PreservesFiniteLimits F'] [PreservesFiniteColimits F']

/-- If `G` preserves quasi-isomorphisms between K-flat complexes and `F'` is exact, then
`G ⋙ F'` preserves quasi-isomorphisms between K-flat complexes. -/
instance preservesKFlatQuasiIso_comp_of_exact : (G ⋙ F').PreservesKFlatQuasiIso where
  quasiIso_map hK hL f _ := by
    have := G.quasiIso_mapHomologicalComplex_map_of_kFlat hK hL f
    exact (inferInstance : QuasiIso ((F'.mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map f)))

/-- The counit exhibiting `L(G) ⋙ D(F')` as a candidate left derived functor of
`(G ⋙ F').mapHomotopyCategory ⋙ Qh`, for an exact functor `F'`: the counit of `L(G)`, followed
by the comparison `F'.mapDerivedCategoryFactorsh` and the composition isomorphism of
`mapHomotopyCategory` (an identity, `Functor.mapHomotopyCategoryCompIso_refl_hom_app`). -/
noncomputable def leftDerivedFunctorCompMapDerivedCategoryRightCounit :
    DerivedCategory.Qh ⋙ (G.leftDerivedFunctor ⋙ F'.mapDerivedCategory) ⟶
      (G ⋙ F').mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  whiskerRight G.leftDerivedFunctorCounit F'.mapDerivedCategory ≫
    whiskerLeft (G.mapHomotopyCategory (ComplexShape.up ℤ)) F'.mapDerivedCategoryFactorsh.hom ≫
    whiskerRight (mapHomotopyCategoryCompIso (Iso.refl (G ⋙ F')) (ComplexShape.up ℤ)).hom
      DerivedCategory.Qh

/-- The counit `Functor.leftDerivedFunctorCompMapDerivedCategoryRightCounit` is `D(F')` applied to
the counit of `L(G)`, followed by the comparison `F'.mapDerivedCategoryFactorsh`. -/
@[reassoc]
lemma leftDerivedFunctorCompMapDerivedCategoryRightCounit_app
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (leftDerivedFunctorCompMapDerivedCategoryRightCounit G F').app K =
      F'.mapDerivedCategory.map (G.leftDerivedFunctorCounit.app K) ≫
        F'.mapDerivedCategoryFactorsh.hom.app
          ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) := by
  simp [leftDerivedFunctorCompMapDerivedCategoryRightCounit,
    mapHomotopyCategoryCompIso_refl_hom_app]

/-- For an exact functor `F'`, `L(G) ⋙ D(F')`, equipped with
`leftDerivedFunctorCompMapDerivedCategoryRightCounit`, is a left derived functor of
`(G ⋙ F').mapHomotopyCategory ⋙ Qh`: on a K-flat complex the counit of `L(G)` is an
isomorphism, and so is the comparison `F'.mapDerivedCategoryFactorsh`. -/
instance isLeftDerivedFunctor_leftDerivedFunctor_comp_mapDerivedCategory :
    (G.leftDerivedFunctor ⋙ F'.mapDerivedCategory).IsLeftDerivedFunctor
      (leftDerivedFunctorCompMapDerivedCategoryRightCounit G F')
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := by
  rw [(G ⋙ F').isLeftDerivedFunctor_iff_isIso_app_of_kFlat]
  intro K hK
  have := G.isIso_leftDerivedFunctorCounit_app_of_kFlat K hK
  rw [leftDerivedFunctorCompMapDerivedCategoryRightCounit_app]
  infer_instance

/-- **Postcomposition with an exact functor**: for `G` preserving quasi-isomorphisms between
K-flat complexes and an exact functor `F'`, `L(G ⋙ F') ≅ L(G) ⋙ D(F')`. -/
noncomputable def leftDerivedFunctorCompMapDerivedCategoryRightIso :
    (G ⋙ F').leftDerivedFunctor ≅ G.leftDerivedFunctor ⋙ F'.mapDerivedCategory :=
  leftDerivedUnique (G.leftDerivedFunctor ⋙ F'.mapDerivedCategory) (G ⋙ F').leftDerivedFunctor
    (G ⋙ F').leftDerivedFunctorCounit (leftDerivedFunctorCompMapDerivedCategoryRightCounit G F')
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))

end CompRight

end CategoryTheory.Functor
