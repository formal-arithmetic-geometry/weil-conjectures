/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q79
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import WeilConjectures.ZetaFunction.Weights
public import WeilConjectures.ZetaFunction.CohomologicalFamily
public import WeilConjectures.ZetaLinearAlgebra.ReciprocalRoots
import Sheaf.LinearAlgebra.FrobeniusModuleWeights
import Sheaf.Paper.WeilCohomologyScalarExtensionQlbar

/-!
# Weight of reciprocal roots

Source: `literature/blueprint/master/blueprint/sec-zeta-weil/sk-prop-rootpurity/`
`prop-weight-purity-roots.md`
(node `prop-weight-purity-roots`).
-/

@[expose] public section
set_option autoImplicit false
universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

/-- In the smooth-proper cohomological family, every reciprocal root in degree `i` has
complex absolute value `q^(i/2)`, by scalar extension to the algebraically closed coefficient
field and ordinary cohomological purity.
Source: blueprint node `prop-weight-purity-roots`, order 2897
(blueprint: prop-weight-purity-roots).

Proof outline: reciprocal roots of the determinant factor are the Frobenius eigenvalues;
scalar extension identifies the ordinary coefficient fields; ordinary cohomological purity
then gives the stated absolute value. -/
theorem reciprocalRoot_weight
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    [Fact (ringChar D.k₀ ≠ l)]
    (X₀ : Scheme.{u}) [X₀.Over (Spec (CommRingCat.of D.k₀))]
    (d : ℕ) [IsProper (X₀ ↘ Spec (CommRingCat.of D.k₀))]
    [SmoothOfRelativeDimension d (X₀ ↘ Spec (CommRingCat.of D.k₀))]
    [GeometricallyConnected (X₀ ↘ Spec (CommRingCat.of D.k₀))]
    (iota : PadicAlgCl l ≃+* ℂ) (i : ℤ) (hi0 : 0 ≤ i) (hi2d : i ≤ 2 * d)
    (α : PadicAlgCl l)
    (hα : α ∈ (Scheme.frobeniusCharpolyRev D.k₀ l X₀ i).reverse.roots) :
    ‖iota α‖ = (D.q : ℝ) ^ ((i : ℝ) / 2) := by
  sorry

end AlgebraicGeometry
