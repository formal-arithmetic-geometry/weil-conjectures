/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Sheaf.CategoryTheory.SimplicialMatchingObject

/-!
# Matching objects as limits over proper faces

Source: Stacks Project, simplicial.tex, Lemma 0186 (lemma-formula-limit), restricted to
injective proper faces (blueprint: lem-weil-pbc-matching-object-proper-faces).
-/

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
namespace CategoryTheory.SimplicialObject

/-- The property selecting injective proper faces in the over category of `[n]`.
Source: Stacks, Tag 0186 (blueprint: lem-weil-pbc-matching-object-proper-faces). -/
def properFaceProperty (n : ℕ) : ObjectProperty (Over ⦋n⦌) :=
  fun a ↦ a.left.len < n ∧ Function.Injective a.hom.toOrderHom

/-- The category `I_n` of injective proper faces, with commuting triangles as arrows.
Source: Stacks, Tag 0186 (blueprint: lem-weil-pbc-matching-object-proper-faces). -/
abbrev ProperFaceCategory (n : ℕ) := (properFaceProperty n).FullSubcategory

/-- The codimension-one face omitting `i` as an object of `I_(n+1)`.
Source: Stacks, Tag 0186 (blueprint: lem-weil-pbc-matching-object-proper-faces). -/
def properFace (n : ℕ) (i : Fin (n + 2)) : ProperFaceCategory (n + 1) :=
  ⟨Over.mk (SimplexCategory.δ i), Nat.lt_succ_self n,
    SimplexCategory.mono_iff_injective.mp
      (inferInstance : Mono (SimplexCategory.δ i))⟩

/-- The contravariant proper-face diagram `P_n(K)`.
Source: Stacks, Tag 0186 (blueprint: lem-weil-pbc-matching-object-proper-faces). -/
def properFaceDiagram {C : Type u} [Category.{v} C] (K : SimplicialObject C) (n : ℕ) :
    (ProperFaceCategory n)ᵒᵖ ⥤ C :=
  ((properFaceProperty n).ι ⋙ Over.forget ⦋n⦌).op ⋙ K

/-- Degree one: compatible proper-face families are arbitrary pairs, naturally in the
vertex. The same matching object is a limit over proper faces, with components computed
by any face factorization, and its matching map has the prescribed components uniquely.
Source: Stacks, Tag 0186 (blueprint: lem-weil-pbc-matching-object-proper-faces).
Proof: every proper injective face factors through a codimension-one face
[lem-weil-pbc-simplex-face-factorization]. In degree one these are exactly the two vertices,
so restriction is a bijection onto pairs, commuting with precomposition. The product
universal property [lem-weil-pbc-simplicial-matching-object] gives the limit over these
faces; the matching-map identities give all its components and limit uniqueness. -/
theorem matching_object_proper_faces_one {C : Type u} [Category.{v} C] [HasFiniteLimits C]
    (K : SimplicialObject C) (c : Fan (fun _ : Fin 2 ↦ K _⦋0⦌))
    (hc : IsLimit c) (μ : K _⦋1⦌ ⟶ c.pt)
    (hμ : ∀ i : Fin 2, μ ≫ c.proj i = K.δ i) :
    (∃ E : ∀ W : C,
        ((Functor.const _).obj W ⟶ properFaceDiagram K 1) ≃
          (Fin 2 → (W ⟶ K _⦋0⦌)),
      (∀ (W : C) (x : (Functor.const _).obj W ⟶ properFaceDiagram K 1) (i : Fin 2),
        E W x i = x.app (op (properFace 0 i))) ∧
      (∀ (W W' : C) (f : W' ⟶ W)
          (x : (Functor.const _).obj W ⟶ properFaceDiagram K 1) (i : Fin 2),
        E W' ((Functor.const _).map f ≫ x) i = f ≫ E W x i)) ∧
    (∃ π : (Functor.const _).obj c.pt ⟶ properFaceDiagram K 1,
      Nonempty (IsLimit (Cone.mk c.pt π)) ∧
      (∀ (a : ProperFaceCategory 1) (i : Fin 2)
          (ε : a.obj.left ⟶ ⦋0⦌), ε ≫ SimplexCategory.δ i = a.obj.hom →
        π.app (op a) = c.proj i ≫ K.map ε.op) ∧
      (∀ a : ProperFaceCategory 1, μ ≫ π.app (op a) = K.map a.obj.hom.op) ∧
      (∀ μ' : K _⦋1⦌ ⟶ c.pt,
        (∀ a : ProperFaceCategory 1, μ' ≫ π.app (op a) = K.map a.obj.hom.op) →
          μ' = μ)) := by
  sorry

/-- Degrees at least two: restriction to codimension-one faces gives the natural compatible
face-tuple bijection. Every limiting boundary cone is also a limit over all proper faces;
its components are independent of factorization, and characterize its matching map.
Source: Stacks, Tag 0186 (blueprint: lem-weil-pbc-matching-object-proper-faces).
Proof: factor each proper face through a missing vertex using
[lem-weil-pbc-simplex-face-factorization]. Restriction of a compatible family satisfies the
face-pair equations by [lem-weil-pbc-simplex-face-face-identity]. Conversely assign to a
proper face the composite through any missing vertex. Two choices factor through the face
omitting both vertices; the same identity and the tuple equation identify the composites.
This proves independence and, using functoriality [def-weil-pbc-simplicial-object], family
compatibility. The constructions are inverse and commute with precomposition. Apply this
to the boundary projections; composing the resulting bijection with the matching object's
universal property [lem-weil-pbc-simplicial-matching-object] proves the limit property.
Finally the matching-map face equations and functoriality give every proper-face component;
uniqueness follows from the limit property. -/
theorem matching_object_proper_faces_succ_succ {C : Type u} [Category.{v} C]
    [HasFiniteLimits C] (K : SimplicialObject C) (n : ℕ)
    (c : Cone (matchingBoundaryIndex K n).multicospan) (hc : IsLimit c)
    (μ : K _⦋n + 2⦌ ⟶ c.pt)
    (hμ : ∀ i : Fin (n + 3), μ ≫ c.π.app (WalkingMulticospan.left i) = K.δ i) :
    (∃ E : ∀ W : C,
        ((Functor.const _).obj W ⟶ properFaceDiagram K (n + 2)) ≃
          {x : Fin (n + 3) → (W ⟶ K _⦋n + 1⦌) //
            ∀ p : (matchingBoundaryShape n).R,
              x p.val.1 ≫ (matchingBoundaryIndex K n).fst p =
                x p.val.2 ≫ (matchingBoundaryIndex K n).snd p},
      (∀ (W : C) (x : (Functor.const _).obj W ⟶ properFaceDiagram K (n + 2))
          (i : Fin (n + 3)), (E W x).val i = x.app (op (properFace (n + 1) i))) ∧
      (∀ (W W' : C) (f : W' ⟶ W)
          (x : (Functor.const _).obj W ⟶ properFaceDiagram K (n + 2)) (i : Fin (n + 3)),
        (E W' ((Functor.const _).map f ≫ x)).val i = f ≫ (E W x).val i)) ∧
    (∃ π : (Functor.const _).obj c.pt ⟶ properFaceDiagram K (n + 2),
      Nonempty (IsLimit (Cone.mk c.pt π)) ∧
      (∀ (a : ProperFaceCategory (n + 2)) (i : Fin (n + 3))
          (ε : a.obj.left ⟶ ⦋n + 1⦌), ε ≫ SimplexCategory.δ i = a.obj.hom →
        π.app (op a) = c.π.app (WalkingMulticospan.left i) ≫ K.map ε.op) ∧
      (∀ a : ProperFaceCategory (n + 2), μ ≫ π.app (op a) = K.map a.obj.hom.op) ∧
      (∀ μ' : K _⦋n + 2⦌ ⟶ c.pt,
        (∀ a : ProperFaceCategory (n + 2),
          μ' ≫ π.app (op a) = K.map a.obj.hom.op) → μ' = μ)) := by
  sorry

end CategoryTheory.SimplicialObject
