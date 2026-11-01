/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorTraceScalar.VectorTraceScalarAffineTowerData

/-! # Scalar compatibility of ordered affine coefficient descent

Source: blueprint/latest, sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2, Tate coefficient comparisons.
(blueprint: lem-pur-vector-scalar-affine-source-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open WeilConjectures.PurityFiniteSetting
namespace AlgebraicGeometry.Etale.VectorTraceScalar

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  derivedTensor upperStar lowerStar

variable {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]

/-- The recursive source comparison is the specified descended Tate coefficient map.
Source: vector-bundle-purity proof paragraph 2, compatibility of the normalized Tate maps
with pullback and ordered tensor products.
Proof: the balancing family is uniquely determined on local pure root/scalar generators.
Inverse image preserves those generator formulas, hence carries balancing to balancing.
The scalar/single comparison on the flat Tate line identifies the derived line square
with this ordinary square. Shift naturality gives the shifted line square. Induct on d.
At zero the scalar/pullback identity equation identifies the two unit maps. At a successor,
expand affineLinearCoefficientDescentStep. The scalar/pullback tensor equation moves the
scalar tensorator through geometric tensor pullback; the shifted line square moves the
last Tate factor. Pullback-composition coherence joins the chart and projection factors.
Tensorator naturality moves the induction equation through the first tensor factor.
Cancel the inverse descent isomorphisms. The resulting composite is exactly lineSource
followed by the preceding towerSource and the image of the coefficient unit. No tensor
factor is permuted. This works for d=0, N=1, zero rings and empty schemes.
(blueprint: lem-pur-vector-scalar-affine-source-compatibility). -/
theorem affine_source_compatibility (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    affineCoefficient φ N hN hA hB S hS d =
      towerSource φ N hN hA hB S hS d (ordinaryFiniteUnit A S) ≫
        (affineTraceRight B N hB S d).map (unit φ S) := by sorry

end AlgebraicGeometry.Etale.VectorTraceScalar
