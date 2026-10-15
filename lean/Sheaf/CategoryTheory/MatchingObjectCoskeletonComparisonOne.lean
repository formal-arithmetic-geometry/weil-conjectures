module

public import Sheaf.CategoryTheory.CoskeletonMatchingTuples
public import Sheaf.CategoryTheory.ProperFaceMatchingObject

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory

universe u v

/-- The comparison between a degree-one coskeleton term and a limiting boundary.
Source: Stacks Project, simplicial.tex, Lemmas 0183 and 0186.
(blueprint: lem-weil-pbc-matching-object-coskeleton-comparison-one).
The two displayed family equivalences identify maps into the coskeleton term and into
 the boundary limit with the same compatible proper-face families. The representing
comparison is therefore an isomorphism and has the indicated projection equations.
-/
theorem matching_object_comparison_one
    {C : Type u} [Category.{v} C] [HasFiniteLimits C]
    (K : SimplicialObject C)
    (L : SimplicialObject C)
    (ε : (SimplicialObject.truncation 0).obj L ⟶
      (SimplicialObject.truncation 0).obj K)
    (c : K ⟶ L)
    (e : ∀ W : C, (W ⟶ L _⦋1⦌) ≃
      {x : ∀ (k : SimplexCategory.Truncated 0),
          ((SimplexCategory.Truncated.inclusion 0).obj k ⟶ SimplexCategory.mk 1) →
            (W ⟶ K.obj (op ((SimplexCategory.Truncated.inclusion 0).obj k))) //
        ∀ (k' k : SimplexCategory.Truncated 0) (ψ : k' ⟶ k)
          (α : (SimplexCategory.Truncated.inclusion 0).obj k ⟶ SimplexCategory.mk 1),
          x k α ≫ K.map ((SimplexCategory.Truncated.inclusion 0).map ψ).op =
            x k' ((SimplexCategory.Truncated.inclusion 0).map ψ ≫ α)})
    (he : ∀ (W : C) (h : W ⟶ L _⦋1⦌)
      (k : SimplexCategory.Truncated 0)
      (α : (SimplexCategory.Truncated.inclusion 0).obj k ⟶ SimplexCategory.mk 1),
      (e W h).val k α = h ≫ L.map α.op ≫ ε.app (op k))
    (hec : ∀ (k : SimplexCategory.Truncated 0)
      (α : (SimplexCategory.Truncated.inclusion 0).obj k ⟶ SimplexCategory.mk 1),
      (e (K _⦋1⦌) (c.app (op (SimplexCategory.mk 1)))).val k α = K.map α.op)
    (M : Fan (fun _ : Fin 2 => K _⦋0⦌)) (hM : IsLimit M)
    (μ : K _⦋1⦌ ⟶ M.pt)
    (hμ : ∀ i : Fin 2, μ ≫ M.proj i = K.δ i)
    (π : (Functor.const _).obj M.pt ⟶ SimplicialObject.properFaceDiagram K 1)
    (hπ : Nonempty (IsLimit (Cone.mk M.pt π)))
    (hπfac : ∀ (a : SimplicialObject.ProperFaceCategory 1) (i : Fin 2)
      (η : a.obj.left ⟶ ⦋0⦌), η ≫ SimplexCategory.δ i = a.obj.hom →
      π.app (op a) = M.proj i ≫ K.map η.op) :
    ∃ θ : L _⦋1⦌ ⟶ M.pt,
      (∀ i : Fin 2, θ ≫ M.proj i =
        L.δ i ≫ ε.app (op ⟨SimplexCategory.mk 0, Nat.le_refl 0⟩)) ∧
      IsIso θ ∧ c.app (op (SimplexCategory.mk 1)) ≫ θ = μ := by
  sorry

end CategoryTheory
