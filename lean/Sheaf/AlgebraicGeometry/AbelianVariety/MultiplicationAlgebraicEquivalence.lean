module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Sheaf.AlgebraicGeometry.LineAlgebraicEquivalence
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor

/-! # Multiplication on abelian line classes modulo algebraic equivalence

Source: Milne, Abelian Varieties, I Remark 10.19, p. 50, and Corollary 5.4, pp. 22–23.
(blueprint: lem-sfb-abelian-multiplication-algebraic-equivalence)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

/-- Multiplication by `n` pulls a line class back to `n²` times that class modulo algebraic
equivalence, without a symmetry or ampleness hypothesis or a restriction on characteristic.

Source: Milne, Abelian Varieties, I Remark 10.19 and Corollary 5.4.
(blueprint: lem-sfb-abelian-multiplication-algebraic-equivalence)

Proof: tensoring and dualizing families show that algebraic equivalence is a congruence
for the tensor group of line classes. Put `cⱼ = [[j]⁎ N]`. Tensor pullback and composition
(lem-weil-pbc-invertible-pullback-tensor) identify `c₀ = 0` and `c₁ = [N]`: the pullback
along the constant identity map is the pullback of a one-dimensional vector space.
Polarization calculus (lem-sfb-abelian-polarization-calculus) gives
`φ_{[-1]⁎N} = φ_N`. Consequently `D = [-1]⁎N ⊗ Nᵛ` is invariant under every translation,
as follows by distributing tensor pullback over the translated-difference lines.
The homogeneous-line criterion (lem-sfb-abelian-homogeneous-line-algebraic-triviality)
then makes `D` algebraically trivial, hence `c₋₁ = c₁`.
Pull the cube identity (thm-sc-theorem-of-cube) back along `x ↦ ([r]x,x,-x)` for `r ≥ 1`.
Its double sums are `[r+1]`, `[r-1]` and `[0]`, and its triple sum is `[r]`.
Thus `c_{r+1} = 2cᵣ - c_{r-1} + 2c₁`. Starting with `c₀ = 0` and `c₁ = c₁`, induction
on consecutive indices gives `cₙ = n²c₁`, since
`2r² - (r-1)² + 2 = (r+1)²`. The displayed tensor quotient is therefore algebraically
trivial. This arithmetic divides by no integer, so it includes positive characteristic. -/
theorem IsAbelianVariety.multiplication_algebraicEquivalence
    {k : Type u} [Field k] [IsAlgClosed k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety A]
    (N : A.left.Modules) [N.IsInvertible] (n : ℕ) :
    Scheme.Modules.AreAlgebraicallyEquivalent A
      ((Scheme.Modules.tensorPullback ((𝟙 A : A ⟶ A) ^ n).left).obj N ⊗
        (Scheme.Modules.dual N).tensorPow (n ^ 2))
      (𝟙_ A.left.Modules) := by
  sorry

end AlgebraicGeometry
