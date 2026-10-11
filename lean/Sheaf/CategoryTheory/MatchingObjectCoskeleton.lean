/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Sheaf.CategoryTheory.SimplicialMatchingObject

/-!
# Matching object and coskeleton

Source: Stacks Project, simplicial.tex, Lemmas 0183 and 0186; Section 0AMA,
Example 0182 (example-cosk0), for degree one.
(blueprint: lem-weil-pbc-matching-object-coskeleton).
The two statements cover degree one and every degree at least two, respectively.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory

universe u v

/-- The matching object in degree one is the corresponding term of the coskeleton.
Source: Stacks Project, simplicial.tex, Lemmas 0183 and 0186 and example-cosk0.
(blueprint: lem-weil-pbc-matching-object-coskeleton).

Proof for stage 3:
1. Put `V = sk_(d-1) K`. By lem-weil-pbc-coskeleton-matching-tuples (Stacks 0183),
   a coskeleton `(L, ε)` exists, and maps into `L_d` are compatible families indexed
   by all maps `[k] → [d]` with `k ≤ d-1`. The canonical map corresponds to `K`'s
   simplicial operators (def-weil-pbc-simplicial-coskeleton).
2. Restrict these families to injective proper faces. Conversely factor every map
   through a missing face (lem-weil-pbc-simplex-face-factorization). Independence of
   this choice follows by factoring through two missing faces and the face identity
   (lem-weil-pbc-simplex-face-face-identity); compatibility follows from functoriality
   (def-weil-pbc-simplicial-object). This is Stacks 0186's natural bijection.
   In degree one the truncated slice consists of the two vertices, so it is simply
   the product description of example-cosk0, with no compatibility equations.
3. By lem-weil-pbc-matching-object-proper-faces, the given limiting boundary cone
   represents these proper-face families, and its matching map represents the family
   of simplicial operators. Thus `L_d` and the matching object represent the same functor.
4. The unique comparison has the displayed projection equations. Comparing in the
   opposite direction gives its inverse; uniqueness makes the composites identities.
   The canonical and matching maps represent the same family, so their composites agree.
   This uses lem-weil-pbc-coskeleton-matching-tuples and
   lem-weil-pbc-matching-object-proper-faces. -/
theorem matching_object_coskeleton_one
    {C : Type u} [Category.{v} C] [HasFiniteLimits C]
    (K : SimplicialObject C) (M : Fan (fun _ : Fin 2 => K _⦋0⦌))
    (_hM : IsLimit M) (μ : K _⦋1⦌ ⟶ M.pt)
    (_hμ : ∀ i : Fin 2, μ ≫ M.proj i = K.δ i) :
    ∃ (L : SimplicialObject C)
      (ε : (SimplicialObject.truncation 0).obj L ⟶
        (SimplicialObject.truncation 0).obj K),
      L.IsRightKanExtension ε ∧
      ∃ (c : K ⟶ L),
        (SimplicialObject.truncation 0).map c ≫ ε =
          𝟙 ((SimplicialObject.truncation 0).obj K) ∧
        ∃ (θ : L _⦋1⦌ ⟶ M.pt),
          (∀ i : Fin 2, θ ≫ M.proj i =
            L.δ i ≫ ε.app (op ⟨SimplexCategory.mk 0, Nat.le_refl 0⟩)) ∧
          (∀ θ' : L _⦋1⦌ ⟶ M.pt,
            (∀ i : Fin 2, θ' ≫ M.proj i =
              L.δ i ≫ ε.app (op ⟨SimplexCategory.mk 0, Nat.le_refl 0⟩)) → θ' = θ) ∧
          IsIso θ ∧ c.app (op (SimplexCategory.mk 1)) ≫ θ = μ := by
  sorry

/-- The matching object in degree `n + 2` is the corresponding term of the coskeleton.
Source: Stacks Project, simplicial.tex, Lemmas 0183 and 0186 and example-cosk0.
(blueprint: lem-weil-pbc-matching-object-coskeleton).

Proof for stage 3:
1. Put `V = sk_(d-1) K`. By lem-weil-pbc-coskeleton-matching-tuples (Stacks 0183),
   a coskeleton `(L, ε)` exists, and maps into `L_d` are compatible families indexed
   by all maps `[k] → [d]` with `k ≤ d-1`. The canonical map corresponds to `K`'s
   simplicial operators (def-weil-pbc-simplicial-coskeleton).
2. Restrict these families to injective proper faces. Conversely factor every map
   through a missing face (lem-weil-pbc-simplex-face-factorization). Independence of
   this choice follows by factoring through two missing faces and the face identity
   (lem-weil-pbc-simplex-face-face-identity); compatibility follows from functoriality
   (def-weil-pbc-simplicial-object). This is Stacks 0186's natural bijection.
   In degree one the truncated slice consists of the two vertices, so it is simply
   the product description of example-cosk0, with no compatibility equations.
3. By lem-weil-pbc-matching-object-proper-faces, the given limiting boundary cone
   represents these proper-face families, and its matching map represents the family
   of simplicial operators. Thus `L_d` and the matching object represent the same functor.
4. The unique comparison has the displayed projection equations. Comparing in the
   opposite direction gives its inverse; uniqueness makes the composites identities.
   The canonical and matching maps represent the same family, so their composites agree.
   This uses lem-weil-pbc-coskeleton-matching-tuples and
   lem-weil-pbc-matching-object-proper-faces. -/
theorem matching_object_coskeleton
    {C : Type u} [Category.{v} C] [HasFiniteLimits C]
    (K : SimplicialObject C) (n : ℕ)
    (M : Cone (SimplicialObject.matchingBoundaryIndex K n).multicospan)
    (_hM : IsLimit M) (μ : K _⦋n + 2⦌ ⟶ M.pt)
    (_hμ : ∀ i : Fin (n + 3), μ ≫ M.π.app (WalkingMulticospan.left i) = K.δ i) :
    ∃ (L : SimplicialObject C)
      (ε : (SimplicialObject.truncation (n + 1)).obj L ⟶
        (SimplicialObject.truncation (n + 1)).obj K),
      L.IsRightKanExtension ε ∧
      ∃ (c : K ⟶ L),
        (SimplicialObject.truncation (n + 1)).map c ≫ ε =
          𝟙 ((SimplicialObject.truncation (n + 1)).obj K) ∧
        ∃ (θ : L _⦋n + 2⦌ ⟶ M.pt),
          (∀ i : Fin (n + 3), θ ≫ M.π.app (WalkingMulticospan.left i) =
            L.δ i ≫ ε.app (op ⟨SimplexCategory.mk (n + 1), Nat.le_refl (n + 1)⟩)) ∧
          (∀ θ' : L _⦋n + 2⦌ ⟶ M.pt,
            (∀ i : Fin (n + 3), θ' ≫ M.π.app (WalkingMulticospan.left i) =
              L.δ i ≫ ε.app (op ⟨SimplexCategory.mk (n + 1), Nat.le_refl (n + 1)⟩)) →
            θ' = θ) ∧
          IsIso θ ∧ c.app (op (SimplexCategory.mk (n + 2))) ≫ θ = μ := by
  sorry

end CategoryTheory
