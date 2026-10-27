/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.AlgebraicGeometry.LinearGroupSchemes

/-!
# The diagonal torus in SL2

Source: Milne, Algebraic Groups (2017), Section 20g, diagonal matrices in SL2.
(blueprint: def-sfb-sl2-diagonal-torus)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.LinearGroupSchemes

variable (k : Type u) [Field k]

/-- Substitute diag(t,t⁻¹) in the polynomial matrix coordinates.
Source: Milne, Algebraic Groups, Section 20g (blueprint: def-sfb-sl2-diagonal-torus). -/
noncomputable def diagonalTorusPolynomial :
    MvPolynomial (Index.{u} 2 × Index.{u} 2) k →ₐ[k] LaurentPolynomial k :=
  MvPolynomial.aeval (fun p ↦ if p.1 = p.2 then
    if p.1.down = 0 then LaurentPolynomial.T 1 else LaurentPolynomial.T (-1) else 0)

/-- The diagonal substitution kills the determinant-one relation.
Source: Milne, Algebraic Groups, Section 20g (blueprint: def-sfb-sl2-diagonal-torus).
Proof: the two off-diagonal entries are zero and the diagonal entries are t and t⁻¹.
Their product is T(1 + (-1)) = T(0) = 1, so det - 1 evaluates to zero. An algebra
homomorphism killing this generator kills its generated ideal, giving the assertion. -/
theorem diagonalTorusPolynomial_relations :
    ∀ f ∈ specialIdeal k 2, diagonalTorusPolynomial k f = 0 := by
  sorry

/-- The actual coordinate map k[SL2] → k[t,t⁻¹], with entries t,0,0,t⁻¹.
Source: Milne, Algebraic Groups, Section 20g (blueprint: def-sfb-sl2-diagonal-torus). -/
noncomputable def diagonalTorusCoordinates : SpecialAlgebra k 2 →ₐ[k] LaurentPolynomial k :=
  Ideal.Quotient.liftₐ (specialIdeal k 2) (diagonalTorusPolynomial k)
    (diagonalTorusPolynomial_relations k)

/-- The canonical diagonal torus inclusion Gm → SL2, obtained by Spec of its coordinate map.
Source: Milne, Algebraic Groups, Section 20g (blueprint: def-sfb-sl2-diagonal-torus). -/
noncomputable def diagonalTorus : StandardGroupSchemes.multiplicative k ⟶ specialLinear k 2 :=
  StandardGroupSchemes.map k (diagonalTorusCoordinates k)

end AlgebraicGeometry.LinearGroupSchemes
