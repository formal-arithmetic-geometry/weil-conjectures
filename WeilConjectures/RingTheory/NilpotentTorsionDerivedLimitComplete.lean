/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.RingTheory.DerivedCompleteModuleComplex
import Mathlib.RingTheory.Nilpotent.Basic
import WeilConjectures.RingTheory.DerivedCompleteProductsTriangles

/-!
# Derived completeness of limits of nilpotent torsion complexes

A derived limit of a tower of complexes on which every element of `I` acts nilpotently at each
level is derived `I`-complete.

## Implementation details

For fixed `a ∈ I` and a level annihilated by `a^e`, the shift `s` on the product of the constant
tower satisfies `s^e = 0`, so `1 - s` is invertible in the Roos triangle and each level is derived
complete. Closure of derived complete complexes under products and triangles then handles the
given tower; no uniform exponent over levels is needed.

## References

* [Stacks, Tag 091W] (with tensor factor `A[0]`)
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- A derived limit of a tower on which each element of `I` acts nilpotently at each
level is derived `I`-complete. The exponent may depend on the element and the level. -/
theorem isDerivedComplete_of_isDerivedLimit_of_nilpotent
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{v} A)]
    (I : Ideal A) (L : ℕ → DerivedCategory (ModuleCat.{v} A)) [HasProduct L]
    (t : ∀ n : ℕ, L (n + 1) ⟶ L n)
    (h : ∀ (a : A), a ∈ I → ∀ n : ℕ, ∃ e : ℕ, 1 ≤ e ∧ (a ^ e) • 𝟙 (L n) = 0)
    (H : DerivedCategory (ModuleCat.{v} A)) (hH : IsDerivedLimit t H) :
    IsDerivedComplete I H := by
  have hL : ∀ n : ℕ, IsDerivedComplete I (L n) := by
    intro n a ha hP T hT
    obtain ⟨e, _, he⟩ := h a ha n
    obtain ⟨p, δ, hT⟩ := hT
    let K : ℕ → DerivedCategory (ModuleCat.{v} A) := fun _ ↦ L n
    let s : End (∏ᶜ K) := .of (towerProductShift (K := K) (fun _ ↦ a • 𝟙 (L n)))
    have hs (r j : ℕ) : ((s ^ r).asHom) ≫ Pi.π K j = (a ^ r) • Pi.π K (j + r) := by
      induction r generalizing j with
      | zero => simp
      | succ r ih =>
        rw [pow_succ, End.mul_asHom, Category.assoc, ih, Linear.comp_smul]
        have hsπ : (s).asHom ≫ Pi.π K (j + r) = a • Pi.π K (j + r + 1) := by
          simp [s, towerProductShift, K]
        rw [hsπ, smul_smul, pow_succ, Nat.add_assoc]
    have hnil : IsNilpotent s := by
      refine ⟨e, End.ext (Pi.hom_ext _ _ fun j ↦ ?_)⟩
      rw [hs, End.zero_asHom, zero_comp]
      simpa only [K, Linear.comp_smul, Category.comp_id, comp_zero] using
        congrArg (fun z ↦ Pi.π K (j + e) ≫ z) he
    apply Pretriangulated.Triangle.isZero₁_of_isIso₂ _ hT
    exact (isUnit_iff_isIso (1 - s)).1 hnil.isUnit_one_sub
  have hQ : IsDerivedComplete I (∏ᶜ L) :=
    (isDerivedComplete_products_and_triangles I).1 L hL |>.2
  obtain ⟨p, δ, hH⟩ := hH
  exact ((isDerivedComplete_products_and_triangles I).2
    (Pretriangulated.Triangle.mk p (towerTransitionEndomorphism t) δ) hH).2.2 hQ hQ

end DerivedCategory
