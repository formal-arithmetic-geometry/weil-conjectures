module

public import Sheaf.CategoryTheory.CommAlgebraSheafModule
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
Proof: choose i₀ in the nonempty directed index. The composites of the stage structure
maps with p's legs coincide: for any two stages, pass to a common upper bound and use
naturality. Their common value gives O.obj → p.pt, and the fact that ι is a morphism in
Under O, together with hι, identifies σ with its composite with the sheafification unit.
Equip p.pt sectionwise with the resulting O-module structure. By hp, each section is
represented at a stage and equality of representatives is detected at a later stage.
A compatible family of module maps therefore descends uniquely to p.pt: define its value
on a representative using the stage map; the equality criterion proves well-definedness,
and a common upper bound proves additivity and O-linearity. Uniqueness also proves
compatibility with restrictions, so this is the presheaf module colimit.
Module sheafification is left adjoint and preserves this colimit. Ring sheafification and
module sheafification have the same underlying abelian sheafification. Their canonical
comparison is O-linear: check on local stage representatives and use hι and the Under O
identities, then glue. It is an isomorphism and carries the sheafified presheaf legs to ι.
Transporting the module colimit along this cocone isomorphism gives the conclusion.
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
    (ι : F ⟶ (Functor.const I).obj (Under.mk σ))
    (hp : ∀ U : Opens X, Nonempty (IsColimit
      (((evaluation (Opens X)ᵒᵖ CommRingCat).obj (Opposite.op U)).mapCocone p)))
    (hι : ∀ i : I, (ι.app i).right.hom = p.ι.app i ≫
      toSheafify (Opens.grothendieckTopology X) p.pt) :
    Nonempty (IsColimit
      ((commAlgebraSheafModuleFunctor O).mapCocone (Cocone.mk (Under.mk σ) ι))) := by
  sorry

end CategoryTheory
