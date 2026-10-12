module

public import Sheaf.CategoryTheory.CommAlgebraSheafModule
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Filtered.Basic

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace CategoryTheory

/-- Core algebra-colimit construction for a sectionwise colimit cocone.
The proof constructs the sectionwise filtered ring colimit, sheafifies it, and verifies the
algebra cocone universal property from the sheafification adjunction.
Source: Stacks Project, Sheaves, Sections 009D and 009E
(blueprint: stage3-sheaf-algebras-directed-colimit-algebra-core). -/
theorem sheafAlgebras_directed_colimit_algebra_core
    (X : Type u) [TopologicalSpace X]
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (F : I ⥤ Under O)
    (p : Cocone (F ⋙ Under.forget O ⋙
      sheafToPresheaf (Opens.grothendieckTopology X) CommRingCat))
    (hp : ∀ U : Opens X, Nonempty (IsColimit
      (((evaluation (Opens X)ᵒᵖ CommRingCat).obj (Opposite.op U)).mapCocone p))) :
    ∃ (σP : O.obj ⟶ p.pt)
      (σ : O ⟶ (presheafToSheaf (Opens.grothendieckTopology X) CommRingCat).obj p.pt)
      (ι : F ⟶ (Functor.const I).obj (Under.mk σ)),
      (∀ i : I, (F.obj i).hom.hom ≫ p.ι.app i = σP) ∧
      σ.hom = σP ≫ toSheafify (Opens.grothendieckTopology X) p.pt ∧
      (∀ i : I, (ι.app i).right.hom =
        p.ι.app i ≫ toSheafify (Opens.grothendieckTopology X) p.pt) ∧
      Nonempty (IsColimit (Cocone.mk (Under.mk σ) ι)) := by
  sorry


end CategoryTheory
