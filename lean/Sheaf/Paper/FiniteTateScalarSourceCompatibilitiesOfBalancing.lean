/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteTateScalarSourceData

/-! # Source compatibilities from finite Tate balancing

Source: sk-prop-an, cor-pur-vector-bundle-purity.proof.md, paragraph 2;
Stacks 06YN, 06YY, 07A6 and 07A4.
(blueprint: lem-pur-finite-tate-scalar-source-compatibilities-of-balancing)

The specified source arrow is a composite of the scalar tensorator, the canonical
scalar/pullback comparison, and the shifted line map. Coherence of the published
unit comparisons gives its coefficient-unit and zero-power equations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

variable {A B : Type (u + 1)} [CommRing A] [CommRing B]

/--
Source: sk-prop-an, cor-pur-vector-bundle-purity.proof.md, paragraph 2;
Stacks 06YN, 06YY, 07A6 and 07A4.
(blueprint: lem-pur-finite-tate-scalar-source-compatibilities-of-balancing)

For a balancing family satisfying the line normalization, compose the specified
scalar tensorator, scalar/pullback comparison, and shifted line map. Each factor
is invertible for every unbounded input, so the source map is invertible. Naturality
of the scalar tensor-unit and pullback-unit comparisons, followed by cancellation
of their isomorphisms, gives the coefficient-unit equation. Transporting the
scalar right-unit equation through the degree-zero line normalization gives the
zero-power equation. These are exactly the two remaining source predicates.
-/
theorem finite_tate_scalar_source_compatibilities_of_balancing [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (X : Scheme.{u}) (hX : ∀ x : X, IsUnit (N : X.presheaf.stalk x))
    (β : ∀ r : ℕ,
      (Etale.purityScalarSheaf φ X).obj (Scheme.finiteEtaleTateTwist X N A hA r) ≅
        Scheme.finiteEtaleTateTwist X N B hB r)
    (hβ : IsFiniteTateScalarBalancing φ N hA hB X β)
    (hline : IsFiniteTateScalarLineNormalized φ N hA hB X β) :
    IsFiniteTateScalarSourceInvertible φ N hA hB X β ∧
      IsFiniteTateScalarSourceUnitNormalized φ N hA hB X β ∧
      IsFiniteTateScalarSourceZeroNormalized φ N hA hB X β := by
  sorry

end WeilConjectures.PurityFiniteSetting
