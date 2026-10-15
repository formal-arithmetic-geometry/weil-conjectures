/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Sheaf.CategoryTheory.TruncatedCoskeletonFiniteLimits

/-!
# Compatible truncated simplex families in a coskeleton

Source: Stacks Project, Simplicial Methods, Lemma 0183 (lemma-existence-cosk)
(blueprint: lem-weil-pbc-coskeleton-matching-tuples).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

/-- Source: Stacks Project, Simplicial Methods, Lemma 0183 (lemma-existence-cosk)
(blueprint: lem-weil-pbc-coskeleton-matching-tuples).
An `(n - 1)`-coskeleton of the truncation of `K` exists. Maps into its degree `n` term
correspond naturally to compatible families indexed by all maps from degrees at most `n - 1`.
The canonical map corresponds to the family of simplicial operators of `K`.

Proof for stage 3:
1. Apply lem-weil-pbc-truncated-coskeleton-finite-limits to the truncation of `K` at `n - 1`.
   Its degree `j` term is the limit over the opposite truncated simplex slice over `[j]`.
   The projections at the identity maps in truncated degrees are isomorphisms: identity is
   terminal in the slice and initial in its opposite. The projection equations make these
   isomorphisms natural. Comparing them with the counit gives a natural automorphism `a` of
   the truncation (def-weil-pbc-simplicial-coskeleton, def-weil-pbc-simplicial-object).
2. By the limit universal property (def-galois-finite-limits-colimits), maps into the degree
   `n` limit correspond bijectively to compatible families. Postcomposition by `a` is a
   bijection of compatible families and yields the displayed counit formula. Both operations
   commute with precomposition in `W`, giving naturality.
3. The canonical morphism has truncated composite with the counit equal to the identity
   (def-weil-pbc-simplicial-coskeleton). Its simplicial naturality then identifies the
   corresponding family with `K.map α.op` (def-weil-pbc-simplicial-object). -/
theorem exists_coskeleton_matching_tuples
    {C : Type u} [Category.{v} C] [HasFiniteLimits C]
    (K : SimplicialObject C) (n : ℕ) (_hn : 1 ≤ n) :
    let m := n - 1
    let i := SimplexCategory.Truncated.inclusion m
    let V := (truncation m).obj K
    let F := fun W : C ↦
      {x : ∀ (k : SimplexCategory.Truncated m),
          (i.obj k ⟶ SimplexCategory.mk n) → (W ⟶ K.obj (op (i.obj k))) //
        ∀ (k' k : SimplexCategory.Truncated m) (ψ : k' ⟶ k)
          (α : i.obj k ⟶ SimplexCategory.mk n),
          x k α ≫ K.map (i.map ψ).op = x k' (i.map ψ ≫ α)}
    ∃ (L : SimplicialObject C) (ε : (truncation m).obj L ⟶ V),
      L.IsRightKanExtension ε ∧
      ∃ (c : K ⟶ L), (truncation m).map c ≫ ε = 𝟙 V ∧
      ∃ (e : ∀ W : C, (W ⟶ L _⦋n⦌) ≃ F W),
        (∀ (W : C) (h : W ⟶ L _⦋n⦌) (k : SimplexCategory.Truncated m)
          (α : i.obj k ⟶ SimplexCategory.mk n),
          (e W h).val k α = h ≫ L.map α.op ≫ ε.app (op k)) ∧
        (∀ (W' W : C) (g : W' ⟶ W) (h : W ⟶ L _⦋n⦌)
          (k : SimplexCategory.Truncated m) (α : i.obj k ⟶ SimplexCategory.mk n),
          (e W' (g ≫ h)).val k α = g ≫ (e W h).val k α) ∧
        (∀ (k : SimplexCategory.Truncated m) (α : i.obj k ⟶ SimplexCategory.mk n),
          (e (K _⦋n⦌) (c.app (op (SimplexCategory.mk n)))).val k α = K.map α.op) := by
  classical
  dsimp
  obtain ⟨R, ε, hR, hpoint, _⟩ :=
    truncatedCoskeletonFiniteLimits.{u, v, 0, 0} C (n - 1)
  let i := SimplexCategory.Truncated.inclusion (n - 1)
  let V := (truncation (n - 1)).obj K
  let L := R.obj V
  let ε' := ε.app V
  let : L.IsRightKanExtension ε' := hR V
  let c : K ⟶ L := Functor.liftOfIsRightKanExtension _ ε' K (𝟙 V)
  have hc : (truncation (n - 1)).map c ≫ ε' = 𝟙 V :=
    Functor.liftOfIsRightKanExtension_fac _ ε' K (𝟙 V)
  let F := fun W : C ↦
    {x : ∀ (k : SimplexCategory.Truncated (n - 1)),
        (i.obj k ⟶ SimplexCategory.mk n) → (W ⟶ K.obj (op (i.obj k))) //
      ∀ (k' k : SimplexCategory.Truncated (n - 1)) (ψ : k' ⟶ k)
        (α : i.obj k ⟶ SimplexCategory.mk n),
        x k α ≫ K.map (i.map ψ).op = x k' (i.map ψ ≫ α)}
  let J := StructuredArrow (op (SimplexCategory.mk n)) i.op
  let D : J ⥤ C := StructuredArrow.proj _ i.op ⋙ V
  let t := (Functor.RightExtension.mk L ε').coneAt (op (SimplexCategory.mk n))
  let ht : IsLimit t := (hpoint V).some _
  let coneOf : ∀ W : C, F W → Cone D := fun W x ↦
    { pt := W
      π :=
        { app := fun j ↦ x.val j.right.unop j.hom.unop
          naturality := by
            intro j j' f
            dsimp
            rw [Category.id_comp]
            have hw := congrArg Quiver.Hom.unop (StructuredArrow.w f)
            dsimp at hw
            rw [← hw]
            exact (x.property _ _ f.right.unop j.hom.unop).symm } }
  let family : ∀ W : C, (W ⟶ L _⦋n⦌) → F W := fun W h ↦
    ⟨fun k α ↦ h ≫ L.map α.op ≫ ε'.app (op k), by
      intro k' k ψ α
      have hh := ε'.naturality ψ.op
      change L.map (i.map ψ).op ≫ ε'.app (op k') =
        ε'.app (op k) ≫ K.map (i.map ψ).op at hh
      simp only [op_comp, L.map_comp, Category.assoc, hh]⟩
  let e : ∀ W : C, (W ⟶ L _⦋n⦌) ≃ F W := fun W ↦
    { toFun := family W
      invFun := fun x ↦ ht.lift (coneOf W x)
      left_inv := by
        intro h
        apply ht.hom_ext
        intro j
        rw [ht.fac]
        rfl
      right_inv := by
        intro x
        apply Subtype.ext
        funext k α
        exact ht.fac (coneOf W x) (StructuredArrow.mk α.op) }
  refine ⟨L, ε', hR V, c, hc, e, ?_, ?_, ?_⟩
  · intro W h k α
    rfl
  · intro W' W g h k α
    change (g ≫ h) ≫ L.map α.op ≫ ε'.app (op k) =
      g ≫ h ≫ L.map α.op ≫ ε'.app (op k)
    rw [Category.assoc]
  · intro k α
    change c.app (op (SimplexCategory.mk n)) ≫ L.map α.op ≫ ε'.app (op k) = K.map α.op
    have hck := NatTrans.congr_app hc (op k)
    change c.app (op (i.obj k)) ≫ ε'.app (op k) = 𝟙 _ at hck
    rw [← Category.assoc, ← c.naturality, Category.assoc]
    exact (congrArg (fun f ↦ K.map α.op ≫ f) hck).trans (Category.comp_id _)

end CategoryTheory.SimplicialObject
