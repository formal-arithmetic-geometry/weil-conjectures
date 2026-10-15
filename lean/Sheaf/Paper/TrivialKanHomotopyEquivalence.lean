/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-!
# A trivial Kan fibration is a homotopy equivalence

Source: Stacks Project, Simplicial, Lemma 08NS (label `lemma-trivial-kan-homotopy`),
using Lemma 08NM (label `lemma-trivial-kan`), and Definition 019K (label
`definition-homotopy`) (blueprint: lem-weil-pbc-trivial-kan-homotopy-equivalence).
-/

@[expose] public section

universe u

open CategoryTheory
open MonoidalCategory
open Simplicial

namespace SSet

/-- A trivial Kan fibration admits a section and a simplicial homotopy from the
identity to the composite with that section.

(blueprint: lem-weil-pbc-trivial-kan-homotopy-equivalence)

Source: Stacks Project, Simplicial, Lemma 08NS (`lemma-trivial-kan-homotopy`),
using Lemma 08NM (`lemma-trivial-kan`) and Definition 019K (`definition-homotopy`).

1. Apply `lem-weil-pbc-trivial-kan-lifts-monomorphisms` (08NM) to the degreewise
   injection `∅ ⟶ Y`, the unique map to `X`, and `𝟙 Y`. The lift is a section
   `g : Y ⟶ X` with `g ≫ p = 𝟙 Y`.
2. The boundary of `Δ[1]` consists in every degree of the two constant simplices
   (`def-weil-pbc-trivial-kan-fibration`, `def-weil-pbc-simplicial-set`). Thus
   `X × ∂Δ[1]` is two disjoint copies of `X`, and its inclusion into `X ⊗ Δ[1]`
   is degreewise injective. Map these copies to `X` by `𝟙 X` and `p ≫ g`.
   Map the cylinder to `Y` by its projection to `X` followed by `p`.
   The square commutes: both endpoint maps become `p`, since `g ≫ p = 𝟙 Y`.
3. Apply `lem-weil-pbc-trivial-kan-lifts-monomorphisms` again to this square.
   The lift `h` restricts to `𝟙 X` and `p ≫ g`, giving the displayed equations.
   These equations give the required homotopy; together with the strict section
   equation they make `g` a homotopy inverse to `p`. -/
theorem exists_section_homotopy_equivalence
    {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : SSet.modelCategoryQuillen.I.rlp p) :
    ∃ (g : Y ⟶ X),
      g ≫ p = 𝟙 Y ∧
        ∃ (h : X ⊗ Δ[1] ⟶ X),
          SSet.ι₀ ≫ h = 𝟙 X ∧ SSet.ι₁ ≫ h = p ≫ g := by
  classical
  have hp' : (MorphismProperty.monomorphisms SSet.{u}).rlp p := by
    rwa [SSet.rlp_monomorphisms]
  have : HasLiftingProperty (⊥ : Y.Subcomplex).ι p := hp' _ inferInstance
  let sq₀ : CommSq (Subcomplex.isInitialBot.to X) (⊥ : Y.Subcomplex).ι p (𝟙 Y) :=
    ⟨Subcomplex.isInitialBot.hom_ext _ _⟩
  let g := sq₀.lift
  have hg : g ≫ p = 𝟙 Y := sq₀.fac_right
  refine ⟨g, hg, ?_⟩
  -- The two copies of X forming the boundary of its cylinder.
  let Z : SSet.{u} :=
    { obj := fun n ↦ X.obj n ⊕ X.obj n
      map := fun f ↦ ↾(Sum.map (X.map f) (X.map f))
      map_id := by intro n; ext x; cases x <;> simp
      map_comp := by intro n m k f t; ext x; cases x <;> simp }
  let j : Z ⟶ X ⊗ Δ[1] :=
    { app := fun n ↦ ↾(Sum.elim (SSet.ι₀.app n) (SSet.ι₁.app n))
      naturality := by
        intro n m f
        ext x
        cases x with
        | inl x => exact ConcreteCategory.congr_hom (SSet.ι₀.naturality f) x
        | inr x => exact ConcreteCategory.congr_hom (SSet.ι₁.naturality f) x }
  have hj : Mono j := by
    have hmono : ∀ n, Mono (j.app n) := by
      rintro ⟨⟨n⟩⟩
      apply (CategoryTheory.mono_iff_injective _).2
      intro x y hxy
      cases x with
      | inl x =>
        cases y with
        | inl y => exact congrArg Sum.inl (congrArg Prod.fst hxy)
        | inr y =>
          have h := congrArg (fun t ↦ t.2 0) hxy
          simp [j] at h
      | inr x =>
        cases y with
        | inl y =>
          have h := congrArg (fun t ↦ t.2 0) hxy
          simp [j] at h
        | inr y => exact congrArg Sum.inr (congrArg Prod.fst hxy)
    exact NatTrans.mono_of_mono_app j
  let a : Z ⟶ X :=
    { app := fun n ↦ ↾(Sum.elim id ((p ≫ g).app n))
      naturality := by
        intro n m f
        ext x
        cases x with
        | inl x => rfl
        | inr x => exact ConcreteCategory.congr_hom ((p ≫ g).naturality f) x }
  have : HasLiftingProperty j p := hp' _ hj
  let sq : CommSq a j p (CartesianMonoidalCategory.fst X Δ[1] ≫ p) := by
    constructor
    ext n x
    cases x with
    | inl x => rfl
    | inr x =>
      have h := congrArg (fun t ↦ t.app n x) (show (p ≫ g) ≫ p = p by
        simp [Category.assoc, hg])
      exact h
  refine ⟨sq.lift, ?_, ?_⟩
  · ext n x
    exact congrArg (fun t : Z ⟶ X ↦ t.app n (Sum.inl x)) sq.fac_left
  · ext n x
    exact congrArg (fun t : Z ⟶ X ↦ t.app n (Sum.inr x)) sq.fac_left

end SSet
