module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
import Sheaf.CategoryTheory.CechResolutionColumns
import Sheaf.CategoryTheory.CechResolutionDoubleComplex
import Sheaf.CategoryTheory.CechResolutionTotal

/-! General-universe Cech double complex comparison. -/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [HasFiniteWidePullbacks C]
  [HasSheafify J AddCommGrpCat.{v}]

/-- The independent-universe Cech double-complex comparison needed for the spectral sequence.

This packages the construction of the double complex and its column and total homology
identifications.  The construction is the universe-lifted version of the equal-universe
`Sheaf.exists_cechDoubleComplex`; its proof follows the same injective-resolution and
Cech-acyclicity argument, with the necessary `ULift` comparisons.

(source: `literature/blueprint/master/blueprint/sec-picard-framework/`
`sk-thm-picard-cech/lem-sc-cech-spectral.md`, Steps 1--2)
Proof: construct one universe-lifted injective-resolution Cech bicomplex,
prove its column comparisons by evaluation and universe transport, prove its
 total comparison using injective Cech acyclicity and the augmentation, and
combine those compatible comparisons.  The proof remains an open obligation.
(blueprint: stage3-cech-general-double-complex)
STATEMENT-DISPUTED: the cited injective-resolution argument does not establish this
large-site statement from HasExt alone. The planned declarations require an explicit
InjectiveResolution F and equal coefficient/index universes. No counterexample is claimed;
the unresolved obligation is resolution existence in the original sheaf category.
-/
theorem Sheaf.exists_cechDoubleComplex_general
    [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
    (F : Sheaf J AddCommGrpCat.{v}) (X : C)
    {ι : Type w} {U : ι → C} (π : ∀ i, U i ⟶ X) (hπ : Sieve.ofArrows U π ∈ J X) :
    ∃ D : HomologicalComplex₂ AddCommGrpCat.{w} (ComplexShape.up ℕ) (ComplexShape.up ℕ),
      (∀ q : ℕ, Nonempty
        (((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) q).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D ≅
        (cechComplexFunctor fun i ↦ Over.mk (π i)).obj
          ((Over.forget X).op ⋙ F.cohomologyPresheaf q))) ∧
      ∀ n : ℕ, Nonempty ((D.total (ComplexShape.up ℕ)).homology n ≅ F.H' n X) := by sorry

end CategoryTheory
