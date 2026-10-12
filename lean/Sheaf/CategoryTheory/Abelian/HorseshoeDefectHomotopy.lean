/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Removing a signed differential defect

The componentwise injective extension argument underlying Stacks Project, Tag 013R.
(blueprint: lem-weil-pbc-horseshoe-defect-homotopy).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.InjectiveResolution

/-- A degree-one cocycle on an augmented resolution with a compatible degree-minus-one
component is a signed coboundary.

Source: Stacks Project, Tag 013R, the inductive null-homotopy construction.
Proof: extend `e` across the monic augmentation into the injective object `J^0` to get
`k^0`. The map `k^0 d_J - E^0` vanishes on the augmentation by the compatibility
identity, so exactness and injectivity extend it across `d_I^0` to obtain `k^1`.
Inductively, suppose `d_I^n k^{n+1} = k^n d_J^n - E^n`. Multiplying by `d_J^{n+1}`
and using the cocycle identity shows that `k^{n+1} d_J^{n+1} - E^{n+1}` vanishes
on `d_I^n`. Exactness at degree `n+1` and injectivity of `J^{n+2}` extend this map
across `d_I^{n+1}`, producing `k^{n+2}`. Dependent recursion assembles the maps.
This proves the displayed identity at every degree, including degree zero.
(blueprint: lem-weil-pbc-horseshoe-defect-homotopy) -/
theorem horseshoe_defect_homotopy
    {C : Type u} [Category.{v} C] [Abelian C] {U V : C}
    (I : InjectiveResolution U) (J : InjectiveResolution V)
    (E : ∀ n : ℕ, I.cocomplex.X n ⟶ J.cocomplex.X (n + 1))
    (e : U ⟶ J.cocomplex.X 0)
    (hE : ∀ n : ℕ, E n ≫ J.cocomplex.d (n + 1) (n + 2) +
      I.cocomplex.d n (n + 1) ≫ E (n + 1) = 0)
    (he : I.ι.f 0 ≫ E 0 = e ≫ J.cocomplex.d 0 1) :
    ∃ k : ∀ n : ℕ, I.cocomplex.X n ⟶ J.cocomplex.X n,
      I.ι.f 0 ≫ k 0 = e ∧ ∀ n : ℕ,
        k n ≫ J.cocomplex.d n (n + 1) -
          I.cocomplex.d n (n + 1) ≫ k (n + 1) = E n := by
  classical
  let k₀ : I.cocomplex.X 0 ⟶ J.cocomplex.X 0 := Injective.factorThru e (I.ι.f 0)
  have hk₀ : I.ι.f 0 ≫ k₀ = e := Injective.comp_factorThru _ _
  have hz₀ : I.ι.f 0 ≫ (k₀ ≫ J.cocomplex.d 0 1 - E 0) = 0 := by
    rw [Preadditive.comp_sub, ← Category.assoc, hk₀, he, sub_self]
  let k₁ : I.cocomplex.X 1 ⟶ J.cocomplex.X 1 :=
    I.exact₀.descToInjective (k₀ ≫ J.cocomplex.d 0 1 - E 0) hz₀
  have hk₁ : I.cocomplex.d 0 1 ≫ k₁ = k₀ ≫ J.cocomplex.d 0 1 - E 0 :=
    I.exact₀.comp_descToInjective _ _
  let T := fun n : ℕ ↦ Σ' a : I.cocomplex.X n ⟶ J.cocomplex.X n,
    Σ' b : I.cocomplex.X (n + 1) ⟶ J.cocomplex.X (n + 1),
      I.cocomplex.d n (n + 1) ≫ b = a ≫ J.cocomplex.d n (n + 1) - E n
  let step : ∀ n : ℕ, T n → T (n + 1) := by
    intro n s
    obtain ⟨a, b, hab⟩ := s
    have hz : I.cocomplex.d n (n + 1) ≫
        (b ≫ J.cocomplex.d (n + 1) (n + 2) - E (n + 1)) = 0 := by
      rw [Preadditive.comp_sub, ← Category.assoc, hab, Preadditive.sub_comp,
        Category.assoc, HomologicalComplex.d_comp_d, comp_zero, zero_sub]
      rw [eq_neg_of_add_eq_zero_left (hE n), neg_neg, sub_self]
    exact ⟨b, (I.exact_succ n).descToInjective
      (b ≫ J.cocomplex.d (n + 1) (n + 2) - E (n + 1)) hz,
      (I.exact_succ n).comp_descToInjective _ _⟩
  let seq : ∀ n : ℕ, T n := fun n ↦ Nat.rec ⟨k₀, k₁, hk₁⟩ step n
  refine ⟨fun n ↦ (seq n).1, hk₀, ?_⟩
  intro n
  have hn := (seq n).2.2
  have hnext : (seq (n + 1)).1 = (seq n).2.1 := by
    change (step n (seq n)).1 = (seq n).2.1
    obtain ⟨a, b, hab⟩ := seq n
    rfl
  change (seq n).1 ≫ J.cocomplex.d n (n + 1) -
    I.cocomplex.d n (n + 1) ≫ (seq (n + 1)).1 = E n
  rw [hnext, hn]
  exact sub_sub_cancel _ _

end CategoryTheory.InjectiveResolution
