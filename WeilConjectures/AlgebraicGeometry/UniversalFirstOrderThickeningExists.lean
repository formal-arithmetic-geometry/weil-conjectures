/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import WeilConjectures.AlgebraicGeometry.UniversalFirstOrderThickening
import WeilConjectures.AlgebraicGeometry.Thickening
import WeilConjectures.AlgebraicGeometry.UniversalThickeningAffineCase
import WeilConjectures.AlgebraicGeometry.UniversalThickeningOpenPieces
import WeilConjectures.RingTheory.UniversalFirstOrderThickening
import WeilConjectures.AlgebraicGeometry.UniversalFirstOrderThickeningExistence

/-!
# Existence and uniqueness of universal first order thickenings

## References

* [Stacks Project, Tag 04F3](https://stacks.math.columbia.edu/tag/04F3)
* [Stacks Project, Tag 04F2](https://stacks.math.columbia.edu/tag/04F2)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A formally unramified morphism admits a universal first order thickening, and any two
such thickenings admit exactly one compatible morphism, which is an isomorphism. -/
theorem FormallyUnramified.exists_universalFirstOrderThickening {Z X : Scheme.{u}}
    (h : Z ⟶ X) [FormallyUnramified h] :
    (∃ (Z' : Scheme.{u}) (i : Z ⟶ Z') (h' : Z' ⟶ X),
      IsUniversalFirstOrderThickening h i h') ∧
    ∀ (Z₁ Z₂ : Scheme.{u}) (i₁ : Z ⟶ Z₁) (h₁ : Z₁ ⟶ X)
      (i₂ : Z ⟶ Z₂) (h₂ : Z₂ ⟶ X),
      IsUniversalFirstOrderThickening h i₁ h₁ →
      IsUniversalFirstOrderThickening h i₂ h₂ →
        (∃! φ : Z₁ ⟶ Z₂, φ ≫ h₂ = h₁ ∧ i₁ ≫ φ = i₂) ∧
          ∀ φ : Z₁ ⟶ Z₂, φ ≫ h₂ = h₁ → i₁ ≫ φ = i₂ → IsIso φ := by
  constructor
  · exact FormallyUnramified.exists_universalFirstOrderThickening_existence h
  · intro Z₁ Z₂ i₁ h₁ i₂ h₂ H₁ H₂
    exact IsUniversalFirstOrderThickening.unique h i₁ h₁ i₂ h₂ H₁ H₂

end AlgebraicGeometry
