/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.Paper.VectorTraceScalarData

/-! # Ordered affine scalar induction from projective traces

Source: blueprint/latest, sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2.
(blueprint: lem-pur-vector-scalar-affine-induction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open WeilConjectures.PurityFiniteSetting
namespace AlgebraicGeometry.Etale.VectorTraceScalar

variable {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]

/-- The scalar square for every ordered affine tower follows from the projective
second-projection trace square over every Noetherian base.
Source: vector-bundle-purity proof paragraph 2; scalar-descent proof Steps 5--8.
Proof: for the standard open immersion, the inverse open scalar map is the left mate
of inverse scalar/pullback. Its open-counit equation, followed by proper direct image
and the assumed projective trace equation, gives the affine-line trace equation.
Tensor this with each ordered shifted Tate input. The compact-support projection
square, tensorator naturality and the unit equation give the affine-line counit
square at every such input. Induct on the coordinate count. Rank zero uses the identity
adjunction. At a successor expand the composite counit and factor the compact scalar
map by its composition square. Use the line counit square, naturality of the outer
compact scalar map, then the induction hypothesis. Ordered coefficient descent gives
exactly affineCoefficient. Refinement coherence identifies the resulting map with the
chosen compactification map. All intermediate bases are Noetherian and the Tate inputs
are shifted flat degree-zero sheaves, so the comparison hypotheses hold. No tensor
factor is permuted; zero rings, N=1 and empty schemes are included.
(blueprint: lem-pur-vector-scalar-affine-induction). -/
theorem affine_of_projective (N : ℕ) (hN : 0 < N) (φ : A →+* B)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (hp : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      projective φ N hN hA hB T hT ≫ projectiveLineTrace N hN B hB T hT =
        (scalarExtension φ T).map (projectiveLineTrace N hN A hA T hT) ≫ unit φ T)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
    ∀ d : ℕ, affine φ N hN hA hB S hS d ≫ affineTrace N hN B hB S hS d =
        (scalarExtension φ S).map (affineTrace N hN A hA S hS d) ≫ unit φ S := by sorry

end AlgebraicGeometry.Etale.VectorTraceScalar
