/-
Copyright (c) 2026 SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Limits.Shapes.Products

import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Sites.Limits
import Sheaf.CategoryTheory.ColimitSystemArrowProductTransitions
import Sheaf.CategoryTheory.ColimitSystemTransitionIdentityDefect

/-! # Transitions on an augmented product of direct images

Source: Stacks Project, Sites, Lemma 0EXZ, product and transition construction.
(blueprint: lem-weil-pbc-colimit-system-product-transitions)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The arrow-indexed product construction gives compatible transitions for any family
of maps to coefficient sheaves. No injectivity or monicity is required here.
Source: Stacks Project, Sites, Lemma 0EXZ, displayed product and transition formula.
(blueprint: lem-weil-pbc-colimit-system-product-transitions)

The product part follows the source; the extra-factor correction for the absent
identity law is an argument by X3.

Proof in words: write R_a for pushforward along a, and c_ab : R_a R_b ≅ R_ab
for its composition comparison. Set B_j = product over t : j → k of R_t A_k.
The map B_j → R_a B_k has t-component the projection indexed by a composed with t,
followed by c_at inverse. Pushforward preserves products since it is a right adjoint.
Checking projections proves its cocycle, using associativity of composition and the
coherence of the pushforward comparisons. The maps d_j : F_j → B_j with components
phi_t followed by R_t(i_k) commute with these transitions by the given cocycle.
Let e_j be phi_id transported through R_id ≅ Id. Applying the cocycle with an
identity arrow shows e_j is idempotent and phi_a R_a(e_k) = phi_a = e_j phi_a.
Enlarge B_j to A_j × B_j and set the extra component of every transition to zero;
its product component is the preceding map after the second projection.
The extra component of gamma_j is (1-e_j)i_j. It commutes with every transition
because phi_a R_a(1-e_k) = 0, while the product component commutes as above.
The enlarged transitions satisfy the cocycle because their extra components vanish
and their product components satisfy the previously verified identity. This also
covers nonunital systems, including zero identity transitions; if e_j = 1 the extra
component of gamma_j is zero and the usual construction is recovered. -/
theorem exists_colimitSystem_product_transitions
    {J : Type u} [SmallCategory J]
    (F : J ⥤ Cat.{u, u}) (T : ∀ j : J, GrothendieckTopology (F.obj j))
    [∀ (j k : J) (a : j ⟶ k), (F.map a).toFunctor.IsContinuous (T j) (T k)]
    (Fs : ∀ j : J, Sheaf (T j) AddCommGrpCat.{u})
    (φ : ∀ {j k : J} (a : j ⟶ k),
      Fs j ⟶ ((F.map a).toFunctor.sheafPushforwardContinuous
        AddCommGrpCat.{u} (T j) (T k)).obj (Fs k))
    (hφ : ∀ {j k l : J} (a : j ⟶ k) (b : k ⟶ l),
      φ (a ≫ b) = φ a ≫
        ((F.map a).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u}
          (T j) (T k)).map (φ b) ≫
        (Functor.sheafPushforwardContinuousComp'
          (eqToIso (congrArg Cat.Hom.toFunctor (F.map_comp a b).symm))
          AddCommGrpCat.{u} (T j) (T k) (T l)).hom.app (Fs l))
    (A : ∀ j : J, Sheaf (T j) AddCommGrpCat.{u}) (ι : ∀ j, Fs j ⟶ A j) :
    let R := fun {j k : J} (a : j ⟶ k) ↦
      (F.map a).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u} (T j) (T k)
    let E := fun j ↦ Functor.sheafPushforwardContinuousId'
      (eqToIso (congrArg Cat.Hom.toFunctor (F.map_id j))) AddCommGrpCat.{u} (T j)
    let B := fun j ↦ ∏ᶜ fun t : Σ k : J, j ⟶ k ↦ (R t.2).obj (A t.1)
    let Gs := fun j ↦ A j ⨯ B j
    let γ := fun j ↦ prod.lift
      ((𝟙 (Fs j) - (φ (𝟙 j) ≫ (E j).hom.app (Fs j) : Fs j ⟶ Fs j)) ≫ ι j)
      (Pi.lift fun t : Σ k : J, j ⟶ k ↦ φ t.2 ≫ (R t.2).map (ι t.1))
    ∃ (ψ : ∀ {j k : J} (a : j ⟶ k), Gs j ⟶ (R a).obj (Gs k)),
      (∀ {j k l : J} (a : j ⟶ k) (b : k ⟶ l),
        ψ (a ≫ b) = ψ a ≫ (R a).map (ψ b) ≫
          (Functor.sheafPushforwardContinuousComp'
            (eqToIso (congrArg Cat.Hom.toFunctor (F.map_comp a b).symm))
            AddCommGrpCat.{u} (T j) (T k) (T l)).hom.app (Gs l)) ∧
      (∀ {j k : J} (a : j ⟶ k), φ a ≫ (R a).map (γ k) = γ j ≫ ψ a) := by
  classical
  let R := fun {j k : J} (a : j ⟶ k) ↦
    (F.map a).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u} (T j) (T k)
  have : ∀ {j k : J} (a : j ⟶ k), PreservesLimits (R a) := by
    intro j k a
    have : PreservesLimits (R a ⋙ sheafToPresheaf (T j) AddCommGrpCat.{u}) := by
      change PreservesLimits
        (sheafToPresheaf (T k) AddCommGrpCat.{u} ⋙
          (Functor.whiskeringLeft _ _ _).obj (F.map a).toFunctor.op)
      infer_instance
    exact preservesLimits_of_reflects_of_preserves (R a) (sheafToPresheaf _ _)
  have : ∀ {j k : J} (a : j ⟶ k), (R a).Additive := by
    intro j k a
    dsimp only [R, Functor.sheafPushforwardContinuous]
    infer_instance
  let C := fun {j k l : J} (a : j ⟶ k) (b : k ⟶ l) ↦
    Functor.sheafPushforwardContinuousComp'
      (eqToIso (congrArg Cat.Hom.toFunctor (F.map_comp a b).symm))
      AddCommGrpCat.{u} (T j) (T k) (T l)
  let E := fun j ↦ Functor.sheafPushforwardContinuousId'
    (eqToIso (congrArg Cat.Hom.toFunctor (F.map_id j))) AddCommGrpCat.{u} (T j)
  let P := fun j (t : Σ k : J, j ⟶ k) ↦ (R t.2).obj (A t.1)
  let B := fun j ↦ ∏ᶜ P j
  let G := fun j ↦ A j ⨯ B j
  let d := fun j ↦ Pi.lift fun t : Σ k : J, j ⟶ k ↦ φ t.2 ≫ (R t.2).map (ι t.1)
  let z := fun j ↦
    (𝟙 (Fs j) - (φ (𝟙 j) ≫ (E j).hom.app (Fs j) : Fs j ⟶ Fs j)) ≫ ι j
  let γ := fun j ↦ prod.lift (z j) (d j)
  change ∃ (ψ : ∀ {j k : J} (a : j ⟶ k), G j ⟶ (R a).obj (G k)),
    (∀ {j k l : J} (a : j ⟶ k) (b : k ⟶ l),
      ψ (a ≫ b) = ψ a ≫ (R a).map (ψ b) ≫ (C a b).hom.app (G l)) ∧
    (∀ {j k : J} (a : j ⟶ k), φ a ≫ (R a).map (γ k) = γ j ≫ ψ a)
  obtain ⟨q, hq, hd⟩ := exists_colimitSystem_arrow_product_transitions F T Fs φ hφ A ι
  have hz {j k : J} (a : j ⟶ k) : φ a ≫ (R a).map (z k) = 0 :=
    colimitSystem_transition_identity_defect F T Fs φ hφ A ι a
  let ψ := fun {j k : J} (a : j ⟶ k) ↦
    prod.lift (0 : G j ⟶ (R a).obj (A k)) (prod.snd ≫ q a) ≫
      inv (prodComparison (R a) (A k) (B k))
  have hψfst {j k : J} (a : j ⟶ k) :
      ψ a ≫ (R a).map prod.fst = 0 := by
    dsimp only [ψ]
    simp only [Category.assoc, inv_prodComparison_map_fst]
    exact prod.lift_fst _ _
  have hψsnd {j k : J} (a : j ⟶ k) :
      ψ a ≫ (R a).map prod.snd = prod.snd ≫ q a := by
    dsimp only [ψ]
    simp only [Category.assoc, inv_prodComparison_map_snd, prod.lift_snd]
    rfl
  have hγfst (j : J) : γ j ≫ prod.fst = z j := prod.lift_fst _ _
  have hγsnd (j : J) : γ j ≫ prod.snd = d j := prod.lift_snd _ _
  refine ⟨ψ, ?_, ?_⟩
  · intro j k l a b
    apply (cancel_mono (prodComparison (R (a ≫ b)) (A l) (B l))).1
    apply prod.hom_ext
    · simp only [Category.assoc, prodComparison_fst]
      rw [hψfst, ← (C a b).hom.naturality prod.fst]
      change 0 = ψ a ≫ (R a).map (ψ b) ≫
        (R a).map ((R b).map prod.fst) ≫ (C a b).hom.app (A l)
      simp only [← Category.assoc, ← Functor.map_comp]
      rw [hψfst]
      simp
    · simp only [Category.assoc, prodComparison_snd]
      rw [hψsnd, ← (C a b).hom.naturality prod.snd]
      change prod.snd ≫ q (a ≫ b) = ψ a ≫ (R a).map (ψ b) ≫
        (R a).map ((R b).map prod.snd) ≫ (C a b).hom.app (B l)
      simp only [← Category.assoc, ← Functor.map_comp]
      rw [hψsnd, (R a).map_comp]
      simp only [← Category.assoc]
      rw [hψsnd]
      simp only [Category.assoc]
      exact congrArg (prod.snd ≫ ·) (hq a b)
  · intro j k a
    apply (cancel_mono (prodComparison (R a) (A k) (B k))).1
    apply prod.hom_ext
    · simp only [Category.assoc, prodComparison_fst]
      rw [← (R a).map_comp, hγfst, hz, hψfst, comp_zero]
    · simp only [Category.assoc, prodComparison_snd]
      rw [← (R a).map_comp, hγsnd, hd a, hψsnd, ← Category.assoc, hγsnd]

end CategoryTheory
