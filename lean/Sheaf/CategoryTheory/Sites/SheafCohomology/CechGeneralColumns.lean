module
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
@[expose] public section
universe w v u
namespace CategoryTheory
open Limits
attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [HasFiniteWidePullbacks C]
  [HasSheafify J AddCommGrpCat.{v}]
/--
The universe-lifted construction and its column comparison.

The intended proof chooses an injective resolution of `F`, forms its Cech double
complex, and transports the equal-universe column comparison along the canonical
`ULift` equivalences.  The construction of that resolution in the original sheaf
category, with an index type in universe `w`, is not currently available from the
`HasExt` hypothesis; this theorem is therefore a named split-off obligation.
(source: `literature/blueprint/master/blueprint/sec-picard-framework/`
`sk-thm-picard-cech/lem-sc-cech-spectral.md`, Steps 1--2;
(blueprint: stage3-cech-general-columns)
-/
theorem Sheaf.exists_cechDoubleComplex_general_columns
    [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
    (F : Sheaf J AddCommGrpCat.{v}) (X : C) {ι : Type w} {U : ι → C}
    (π : ∀ i, U i ⟶ X) (hπ : Sieve.ofArrows U π ∈ J X) :
    ∃ D : HomologicalComplex₂ AddCommGrpCat.{w} (ComplexShape.up ℕ) (ComplexShape.up ℕ),
      ∀ q : ℕ, Nonempty (((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ)
        q).mapHomologicalComplex (ComplexShape.up ℕ)).obj D ≅
        (cechComplexFunctor fun i ↦ Over.mk (π i)).obj
          ((Over.forget X).op ⋙ F.cohomologyPresheaf q)) := by sorry
end CategoryTheory
