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
-- The unchanged covering hypothesis is unnecessary for the column-only assertion.
set_option linter.unusedVariables false in
/-- A double complex whose column cohomology is the Čech complex of the cohomology presheaf.

Put `K q = Cech(U, H^q(F))` and `D^(p,q) = (K q)^p`. Give `D` the
horizontal differential of `K q` and zero vertical differentials. The horizontal
square-zero identity follows from `K q`; the vertical square-zero and commutation
identities follow from the zero differentials. Since both differentials adjacent
to vertical degree `q` are zero, its homology is canonically `D^(p,q)`. Naturality
of the zero-differential homology comparison for horizontal maps assembles these
isomorphisms into an isomorphism of complexes with `K q`.

This proves precisely the column-only existence assertion. The construction does
not assert a total-cohomology comparison or choose an injective resolution.
The covering hypothesis is not needed for this assertion.

Source: the column comparison in blueprint `lem-sc-cech-spectral`, Steps 1--2;
the direct column-only construction and proof are written by this worker.
(blueprint: stage3-cech-general-columns) -/
theorem Sheaf.exists_cechDoubleComplex_general_columns
    [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
    (F : Sheaf J AddCommGrpCat.{v}) (X : C) {ι : Type w} {U : ι → C}
    (π : ∀ i, U i ⟶ X) (hπ : Sieve.ofArrows U π ∈ J X) :
    ∃ D : HomologicalComplex₂ AddCommGrpCat.{w} (ComplexShape.up ℕ) (ComplexShape.up ℕ),
      ∀ q : ℕ, Nonempty (((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ)
        q).mapHomologicalComplex (ComplexShape.up ℕ)).obj D ≅
        (cechComplexFunctor fun i ↦ Over.mk (π i)).obj
          ((Over.forget X).op ⋙ F.cohomologyPresheaf q)) := by
  let K : ℕ → CochainComplex AddCommGrpCat.{w} ℕ := fun q ↦
    (cechComplexFunctor fun i ↦ Over.mk (π i)).obj
      ((Over.forget X).op ⋙ F.cohomologyPresheaf q)
  let D : HomologicalComplex₂ AddCommGrpCat.{w} (ComplexShape.up ℕ)
      (ComplexShape.up ℕ) :=
    { X := fun p ↦
        { X := fun q ↦ (K q).X p
          d := fun _ _ ↦ 0
          shape := by intros; rfl
          d_comp_d' := by intros; simp }
      d := fun p p' ↦
        { f := fun q ↦ (K q).d p p'
          comm' := by intros; simp }
      shape := by
        intro p p' h
        apply HomologicalComplex.Hom.ext
        funext q
        exact (K q).shape p p' h
      d_comp_d' := by
        intro p p' p'' _ _
        apply HomologicalComplex.Hom.ext
        funext q
        exact (K q).d_comp_d p p' p'' }
  refine ⟨D, fun q ↦ ?_⟩
  let e : ∀ p, (D.X p).homology q ≅ (K q).X p := fun p ↦
    (ShortComplex.LeftHomologyData.ofZeros ((D.X p).sc q) rfl rfl).homologyIso
  refine ⟨HomologicalComplex.Hom.isoOfComponents e ?_⟩
  intro p p' h
  change (e p).hom ≫ (K q).d p p' =
    HomologicalComplex.homologyMap (D.d p p') q ≫ (e p').hom
  symm
  exact (ShortComplex.LeftHomologyMapData.ofZeros
    ((HomologicalComplex.shortComplexFunctor _ _ q).map (D.d p p'))
    rfl rfl rfl rfl).homologyMap_comm

end CategoryTheory
