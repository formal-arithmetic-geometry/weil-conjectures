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
(blueprint: lem-weil-pbc-transition-identity-defect)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Source: Stacks Project, Sites, Tag 0EXZ, transition cocycle; nonunital
identity correction written by X3 in the parent node, step 3.
(blueprint: lem-weil-pbc-transition-identity-defect)

Proof in words: set e_k=φ_id followed by the identity comparison E_k.
The cocycle for a and id_k, together with a≫id_k=a and the coherence of the
identity and composition comparisons, says φ_a R_a(e_k)=φ_a. Since pushforward
is additive, φ_a R_a(1-e_k)=φ_a-φ_a=0. Postcomposing with R_a(ι_k) proves
this assertion. The argument also covers zero identity transitions and empty J. -/
theorem colimitSystem_transition_identity_defect
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
    ∀ {j k : J} (a : j ⟶ k),
      φ a ≫ (R a).map
        ((𝟙 (Fs k) - (φ (𝟙 k) ≫ (E k).hom.app (Fs k) : Fs k ⟶ Fs k)) ≫ ι k) =
          0 := by
  sorry

end CategoryTheory
