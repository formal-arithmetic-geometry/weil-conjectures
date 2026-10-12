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
import Sheaf.CategoryTheory.ArrowProductTransitionsCocycle
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-! # Transitions on an augmented product of direct images

Source: Stacks Project, Sites, Lemma 0EXZ, product and transition construction.
(blueprint: lem-weil-pbc-arrow-product-compatible-transitions)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Source: Stacks Project, Sites, Tag 0EXZ, displayed product construction.
(blueprint: lem-weil-pbc-arrow-product-compatible-transitions)

Proof in words: define q_a using preservation of products by R_a. Its t-component
is the projection at a≫t followed by the inverse composition comparison at A_l.
The cocycle is checked after each mapped projection: both composites select the
projection at (a≫b)≫t=a≫(b≫t), and the comparison maps agree by the associativity
coherence of precomposition. For compatibility with d, checking the t-projection
reduces to the assumed cocycle for φ and naturality of the comparison at ι_l.
This argument uses neither identity laws for φ nor any monicity assumption. -/
theorem exists_colimitSystem_arrow_product_transitions
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
    let B := fun j ↦ ∏ᶜ fun t : Σ k : J, j ⟶ k ↦ (R t.2).obj (A t.1)
    let d := fun j ↦ Pi.lift fun t : Σ k : J, j ⟶ k ↦ φ t.2 ≫ (R t.2).map (ι t.1)
    ∃ (q : ∀ {j k : J} (a : j ⟶ k), B j ⟶ (R a).obj (B k)),
      (∀ {j k l : J} (a : j ⟶ k) (b : k ⟶ l),
        q (a ≫ b) = q a ≫ (R a).map (q b) ≫
          (Functor.sheafPushforwardContinuousComp'
            (eqToIso (congrArg Cat.Hom.toFunctor (F.map_comp a b).symm))
            AddCommGrpCat.{u} (T j) (T k) (T l)).hom.app (B l)) ∧
      (∀ {j k : J} (a : j ⟶ k), φ a ≫ (R a).map (d k) = d j ≫ q a) := by
  dsimp
  let R := fun {j k : J} (a : j ⟶ k) ↦
    (F.map a).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u} (T j) (T k)
  let P := fun j (t : Σ k : J, j ⟶ k) ↦ (R t.2).obj (A t.1)
  let d := fun j ↦ Pi.lift fun t : Σ k : J, j ⟶ k ↦ φ t.2 ≫ (R t.2).map (ι t.1)
  obtain ⟨q, hq, hqc⟩ := exists_arrow_product_transitions_cocycle F T A
  refine ⟨q, hqc, ?_⟩
  intro j k a
  have : PreservesLimits (R a) := by
    dsimp [R]
    infer_instance
  apply (isLimitOfHasProductOfPreservesLimit (R a) (P k)).hom_ext
  intro t
  change (φ a ≫ (R a).map (d k)) ≫ (R a).map (Pi.π (P k) t.as) =
    (d j ≫ q a) ≫ (R a).map (Pi.π (P k) t.as)
  rw [Category.assoc, Category.assoc, hq]
  dsimp [d, P, R]
  simp only [← Category.assoc, Pi.lift_π, ← Functor.map_comp]
  rw [hφ]
  simp only [Category.assoc, Functor.map_comp]
  have hn := NatIso.naturality_2
    (Functor.sheafPushforwardContinuousComp'
      (eqToIso (congrArg Cat.Hom.toFunctor (F.map_comp a t.as.2).symm))
      AddCommGrpCat.{u} (T j) (T k) (T t.as.1)) (ι t.as.1)
  exact congrArg (fun f ↦ φ a ≫ (R a).map (φ t.as.2) ≫ f) hn.symm

end CategoryTheory
