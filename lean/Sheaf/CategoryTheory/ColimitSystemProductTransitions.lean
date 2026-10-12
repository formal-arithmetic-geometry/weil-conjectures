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
  sorry

end CategoryTheory
