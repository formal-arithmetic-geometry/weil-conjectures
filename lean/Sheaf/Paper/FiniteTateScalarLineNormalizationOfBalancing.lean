/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteTateScalarSourceData

/-! # Line normalization from finite Tate balancing

Source: sk-prop-an, cor-pur-vector-bundle-purity.proof.md, paragraph 2;
Stacks 06YN, 06YY, 07A6 and 07A4.
(blueprint: lem-pur-finite-tate-scalar-line-normalization-of-balancing)

The scalar/single comparison on each flat Tate line is the ordinary coefficient
extension comparison. The rank-one balancing map and its tensor powers therefore
are isomorphisms, and the degree-zero map is the specified scalar unit.
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
(blueprint: lem-pur-finite-tate-scalar-line-normalization-of-balancing)

For the balancing family supplied by the ordinary coefficient construction,
flatness of every finite Tate line identifies the normalized scalar/single map
with its degree-zero flat representative. The rank-one coefficient formula is
invertible with inverse inserting `1`; tensor-power and shift comparisons preserve
invertibility. At degree zero the map is ordinary multiplication, so the
specified scalar unit and zero-line equation hold by the unit laws.
-/
theorem finite_tate_scalar_line_normalization_of_balancing [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (X : Scheme.{u}) (hX : ∀ x : X, IsUnit (N : X.presheaf.stalk x))
    (β : ∀ r : ℕ,
      (Etale.purityScalarSheaf φ X).obj (Scheme.finiteEtaleTateTwist X N A hA r) ≅
        Scheme.finiteEtaleTateTwist X N B hB r)
    (hβ : IsFiniteTateScalarBalancing φ N hA hB X β) :
    IsFiniteTateScalarLineNormalized φ N hA hB X β := by
  sorry

end WeilConjectures.PurityFiniteSetting
