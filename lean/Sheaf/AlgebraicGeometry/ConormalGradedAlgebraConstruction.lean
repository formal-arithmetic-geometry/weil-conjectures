/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.AlgebraicGeometry.ConormalGradedAlgebraBasic
public import WeilConjectures.RingTheory.AssociatedGradedRing
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # The algebra obtained by descending the ideal-power quotients

Source: Stacks Project, Divisors, Tags 0630 and 0633.
(blueprint: lem-pur-conormal-graded-algebra-construction).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.ConormalGradedAlgebra
variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The algebra construction with its coproduct and normalized affine charts.
This record contains no stalk or finiteness assertion and no symmetric comparison
or augmentation. Source: Stacks Project, Divisors, Tags 0630 and 0633.
(blueprint: lem-pur-conormal-graded-algebra-construction). -/
structure AffineData where
  algebra : Z.CommAlgebraSheaf
  inclusion : ∀ n, piece i n ⟶ algebra.toModule
  coproduct : IsColimit (Cofan.mk algebra.toModule inclusion)
  multiplication : ∀ (m n : ℕ) (U : X.Opens)
    (a : (power i m).val.obj (op U)) (b : (power i n).val.obj (op U))
    (d : (power i (m + n)).val.obj (op U)),
    (powerInclusion i (m + n)).val.app (op U) d =
        (@id Γ(X, U) ((powerInclusion i m).val.app (op U) a)) *
          (@id Γ(X, U) ((powerInclusion i n).val.app (op U) b)) →
      homogeneousClass i algebra inclusion m U a * homogeneousClass i algebra inclusion n U b =
        homogeneousClass i algebra inclusion (m + n) U d
  constants : ∀ (U : X.Opens) (a : (power i 0).val.obj (op U)),
    homogeneousClass i algebra inclusion 0 U a =
      algebra.hom.hom.app (op (i ⁻¹ᵁ U)) (i.app U a)
  affineChart : ∀ U : X.affineOpens,
    ∃ e : algebra.right.obj.obj (op (i ⁻¹ᵁ U.1)) ≅
        CommRingCat.of (Ideal.associatedGraded (i.ker.ideal U)),
      ∀ (n : ℕ) (a : (power i n).val.obj (op U.1)),
        ∃ h : (powerInclusion i n).val.app (op U.1) a ∈ i.ker.ideal U ^ n,
          e.hom (homogeneousClass i algebra inclusion n U.1 a) =
            DirectSum.of (Ideal.associatedGradedPiece (i.ker.ideal U)) n
              (Submodule.Quotient.mk ⟨(powerInclusion i n).val.app (op U.1) a, h⟩)

/-- The ideal-power quotient multiplication descends to the closed subscheme and
its total algebra has the expected normalized affine associated-graded charts.
Source: Stacks Project, Divisors, Tags 0630 and 0633.
(blueprint: lem-pur-conormal-graded-algebra-construction).

Proof: Form the quasi-coherent sheaf cokernels `B_n = I^n/I I^n` on the ambient
scheme. Their multiplication is the multiplication of ideal-power representatives:
changing either representative changes the product by `I^(m+n+1)`. The affine
quotient formula and sheaf separatedness glue the products and verify the ring
laws. Each `B_n` is annihilated by `I`. The normalized closed-immersion unit quotient
identifies it with the pushforward of the fixed module `i^*I^n`, including n=0.
Transport the products and unit through these identifications; fully faithful
pushforward makes their laws hold on the closed subscheme. Sheafify the presheaf
of finite sums of homogeneous sections with this convolution multiplication.
Its maps as a module sheaf are precisely families of maps from the homogeneous
pieces, proving the coproduct property. On an ambient affine `Spec R`, the quotient
pieces have sections `J^n/J^(n+1)` on `Spec(R/J)`. The affine tilde adjunction preserves
the coproduct and identifies its sections with the direct sum of these modules.
The representative multiplication and constant formulas make this identification
an isomorphism of rings with `gr_J(R)`. Every construction respects restriction.
This uses only affine sections of quasi-coherent sheaves; no assertion about arbitrary
sections commuting with infinite sums is needed. The zero ring, n=0, and the empty
closed subscheme satisfy the same construction and formulas. -/
theorem exists_affineData : Nonempty (AffineData i) := by
  sorry

end AlgebraicGeometry.ConormalGradedAlgebra
