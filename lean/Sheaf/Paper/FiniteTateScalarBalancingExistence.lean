/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteTateScalarSourceData

/-! # Existence of finite Tate scalar balancing families

Source: sk-prop-an, cor-pur-vector-bundle-purity.proof.md, paragraph 2;
Stacks 06YN, 06YY, 07A6 and 07A4.
(blueprint: lem-pur-finite-tate-scalar-balancing-existence)

The ordinary coefficient balancing is constructed sectionwise from the formula
`(a tensor z) tensor b ↦ φ(a)b tensor z`, with inverse inserting `1` in the
coefficient factor. Tensor powers and the degree-zero multiplication give the
family in all degrees. The balancing relation proves that the formulas descend
to sheaf tensor products and that the inverse formulas are two-sided.
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
(blueprint: lem-pur-finite-tate-scalar-balancing-existence)

For each degree, use ordinary coefficient multiplication on the degree-zero Tate
sheaf and its tensor powers on positive Tate degrees. On a local pure tensor the
map is `(a tensor z) tensor b ↦ φ(a)b tensor z`; its inverse sends `b tensor z`
to `(1 tensor z) tensor b`. The balancing relations make these formulas
well-defined and inverse, while restriction compatibility makes them sheaf maps.
The root-generator formula, the degree-zero oplax unit, and the successor
formula are then exactly the defining equations of
`IsFiniteTateScalarBalancing`.
-/
theorem finite_tate_scalar_balancing_exists [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (X : Scheme.{u}) (hX : ∀ x : X, IsUnit (N : X.presheaf.stalk x)) :
    ∃ β : ∀ r : ℕ,
        (Etale.purityScalarSheaf φ X).obj (Scheme.finiteEtaleTateTwist X N A hA r) ≅
          Scheme.finiteEtaleTateTwist X N B hB r,
      IsFiniteTateScalarBalancing φ N hA hB X β := by
  sorry

end WeilConjectures.PurityFiniteSetting
