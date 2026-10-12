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

/-- The underlying module cocone of the sheafified algebra colimit is a colimit.
The proof identifies ring and module sheafifications on underlying abelian sheaves and
transports the module colimit structure.
Source: Stacks Project, Modules, Lemma 01AH
(blueprint: stage3-sheaf-algebras-directed-colimit-module-core). -/
theorem sheafAlgebras_directed_colimit_module_core
    (X : Type u) [TopologicalSpace X]
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (F : I ⥤ Under O)
    (p : Cocone (F ⋙ Under.forget O ⋙
      sheafToPresheaf (Opens.grothendieckTopology X) CommRingCat))
    (σ : O ⟶ (presheafToSheaf (Opens.grothendieckTopology X) CommRingCat).obj p.pt)
    (ι : F ⟶ (Functor.const I).obj (Under.mk σ)) :
    Nonempty (IsColimit
      ((commAlgebraSheafModuleFunctor O).mapCocone (Cocone.mk (Under.mk σ) ι))) := by
  sorry

end CategoryTheory
