module

public import Sheaf.CategoryTheory.CoskeletonMatchingTuples
public import Sheaf.CategoryTheory.ProperFaceMatchingObject

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory

universe u v

/-- The comparison between a coskeleton term and a limiting proper-face boundary.
Source: Stacks Project, simplicial.tex, Lemmas 0183 and 0186.
(blueprint: lem-weil-pbc-matching-object-coskeleton-comparison).
The displayed family equivalences identify maps into the coskeleton term and into the
boundary limit with the same compatible proper-face families. The representing
comparison is therefore an isomorphism and has the indicated projection equations.
-/
theorem matching_object_comparison
    {C : Type u} [Category.{v} C] [HasFiniteLimits C]
    (K : SimplicialObject C) (L : SimplicialObject C) (n : ℕ) (ε :
      (SimplicialObject.truncation (n + 1)).obj L ⟶
        (SimplicialObject.truncation (n + 1)).obj K) (c : K ⟶ L)
    (e : ∀ W : C, (W ⟶ L _⦋n + 2⦌) ≃
      {x : ∀ (k : SimplexCategory.Truncated (n + 1)),
          ((SimplexCategory.Truncated.inclusion (n + 1)).obj k ⟶ SimplexCategory.mk (n + 2)) →
            (W ⟶ K.obj (op ((SimplexCategory.Truncated.inclusion (n + 1)).obj k))) //
        ∀ (k' k : SimplexCategory.Truncated (n + 1)) (ψ : k' ⟶ k)
          (α : (SimplexCategory.Truncated.inclusion (n + 1)).obj k ⟶ SimplexCategory.mk (n + 2)),
          x k α ≫ K.map ((SimplexCategory.Truncated.inclusion (n + 1)).map ψ).op =
            x k' ((SimplexCategory.Truncated.inclusion (n + 1)).map ψ ≫ α)})
    (he : ∀ (W : C) (h : W ⟶ L _⦋n + 2⦌)
      (k : SimplexCategory.Truncated (n + 1))
      (α : (SimplexCategory.Truncated.inclusion (n + 1)).obj k ⟶ SimplexCategory.mk (n + 2)),
      (e W h).val k α = h ≫ L.map α.op ≫ ε.app (op k))
    (hec : ∀ (k : SimplexCategory.Truncated (n + 1))
      (α : (SimplexCategory.Truncated.inclusion (n + 1)).obj k ⟶ SimplexCategory.mk (n + 2)),
      (e (K _⦋n + 2⦌) (c.app (op (SimplexCategory.mk (n + 2))))).val k α = K.map α.op)
    (M : Cone (SimplicialObject.matchingBoundaryIndex K n).multicospan)
    (hM : IsLimit M) (μ : K _⦋n + 2⦌ ⟶ M.pt)
    (hμ : ∀ i : Fin (n + 3), μ ≫ M.π.app (WalkingMulticospan.left i) = K.δ i)
    (π : (Functor.const _).obj M.pt ⟶ SimplicialObject.properFaceDiagram K (n + 2))
    (hπ : Nonempty (IsLimit (Cone.mk M.pt π)))
    (hπfac : ∀ (a : SimplicialObject.ProperFaceCategory (n + 2)) (i : Fin (n + 3))
      (η : a.obj.left ⟶ ⦋n + 1⦌), η ≫ SimplexCategory.δ i = a.obj.hom →
      π.app (op a) = M.π.app (WalkingMulticospan.left i) ≫ K.map η.op) :
    ∃ θ : L _⦋n + 2⦌ ⟶ M.pt,
      (∀ i : Fin (n + 3), θ ≫ M.π.app (WalkingMulticospan.left i) =
        L.δ i ≫ ε.app (op ⟨SimplexCategory.mk (n + 1), Nat.le_refl (n + 1)⟩)) ∧
      IsIso θ ∧ c.app (op (SimplexCategory.mk (n + 2))) ≫ θ = μ := by
  sorry

end CategoryTheory
