module

public import Sheaf.CategoryTheory.CechResolutionDoubleComplex
public import Mathlib.Algebra.Homology.Functor

@[expose] public section
universe u v
namespace CategoryTheory

/-- Objectwise comparison isomorphisms for the cohomology of an injective resolution,
with the restriction compatibility needed to assemble them into a natural isomorphism.
Source: blueprint lem-sc-injective-resolution-cohomology-presheaf, Step 2.
(blueprint: lem-sc-injective-resolution-cohomology-presheaf-data) -/
theorem Sheaf.injectiveResolution_cohomologyPresheaf_data
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{v}] [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
    {F : Sheaf J AddCommGrpCat.{v}} (I : InjectiveResolution F) (q : ℕ) :
    ∃ e : ∀ X : Cᵒᵖ,
      ((((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex).asFunctor ⋙
        HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) q).obj X ≅
      (F.cohomologyPresheaf q).obj X,
      ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y),
        ((((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex).asFunctor ⋙
          HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) q).map f ≫
            (e Y).hom = (e X).hom ≫ (F.cohomologyPresheaf q).map f := by
  sorry

end CategoryTheory
