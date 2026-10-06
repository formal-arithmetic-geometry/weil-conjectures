/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmooth

/-!
# Smoothness of relative affine space

We show that the relative affine space `𝔸(n; S) ⟶ S` on a finite index type `n` is smooth of
relative dimension `Nat.card n`, the polynomial algebra `MvPolynomial n R` being standard
smooth of relative dimension `Nat.card n` over `R`
(`Algebra.IsStandardSmoothOfRelativeDimension.mvPolynomial`).

## Main results

- `AlgebraicGeometry.AffineSpace.smoothOfRelativeDimension_over`: `𝔸(n; S) ⟶ S` is smooth
  of relative dimension `Nat.card n`, for finite `n`.
- `AlgebraicGeometry.smoothOfRelativeDimension_affineLine`: the affine line `𝔸¹_R ⟶ Spec R`
  is smooth of relative dimension one.

-/

@[expose] public section

universe u

open CategoryTheory Limits MvPolynomial

namespace AlgebraicGeometry

namespace AffineSpace

variable (n : Type u) [Finite n]

/-- The structure morphism `𝔸(n; Spec R) ⟶ Spec R` is smooth of relative dimension
`Nat.card n`, for finite `n`. -/
lemma smoothOfRelativeDimension_over_Spec (R : CommRingCat.{u}) :
    SmoothOfRelativeDimension (Nat.card n) (𝔸(n; Spec R) ↘ Spec R) := by
  rw [← MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension (Nat.card n))
    (SpecIso n R).inv, SpecIso_inv_over,
    HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension (Nat.card n))]
  refine RingHom.locally_of
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  rw [CommRingCat.hom_ofHom, ← MvPolynomial.algebraMap_eq,
    RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  infer_instance

/-- The structure morphism `𝔸(n; S) ⟶ S` is smooth of relative dimension `Nat.card n`, for
finite `n`. -/
instance smoothOfRelativeDimension_over (S : Scheme.{u}) :
    SmoothOfRelativeDimension (Nat.card n) (𝔸(n; S) ↘ S) := by
  have := smoothOfRelativeDimension_isStableUnderBaseChange (Nat.card n)
  exact MorphismProperty.of_isPullback (isPullback_map (n := n) S.toSpecΓ)
    (smoothOfRelativeDimension_over_Spec n Γ(S, ⊤))

end AffineSpace

/-- The affine line `𝔸¹_R ⟶ Spec R` is smooth of relative dimension one. -/
instance smoothOfRelativeDimension_affineLine (R : Type u) [CommRing R] :
    SmoothOfRelativeDimension 1 (affineLine R ↘ Spec (CommRingCat.of R)) := by
  simpa using AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} (Spec (.of R))

end AlgebraicGeometry
