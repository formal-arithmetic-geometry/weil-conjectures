module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Valuation.Basic

/-!
# Dimension of products of subspaces with a rational residue valuation

Source: the agent auxiliary product-subspace argument supporting Morrison,
`GIT Constructions of Moduli Spaces of Stable Curves and Maps`, Section 2.4, Theorem 5,
printed p. 10;
Stacks Project, Algebra, Tags 00IE and 00IF, for the valuation framework.
The auxiliary is not separately stated in Morrison.
(blueprint: lem-sfb-residue-valuation-product-dimension)
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Submodule

/-- For a DVR subring of `K` containing `k`, with fraction field `K` and canonical residue
map identifying `k` with its residue field, the product of two nonzero finite-dimensional
`k`-subspaces has dimension at least the sum of their dimensions minus one. The product
`V * W` is precisely the span of all products, by `Submodule.mul_def`.

Source: the agent auxiliary for Morrison, Section 2.4, Theorem 5, printed p. 10, using
Stacks Project, Algebra, Tags 00IE and 00IF.
(blueprint: lem-sfb-residue-valuation-product-dimension)

Proof:
1. Apply `lem-sfb-rational-residue-distinct-order-basis` to `V` and `W`. Obtain bases
   `v₁, ..., vᵣ` and `w₁, ..., wₛ` with strictly increasing normalized valuations
   `a₁ < ... < aᵣ` and `b₁ < ... < bₛ`. Nonzeroness gives `r, s ≥ 1`.
2. Expanding in these bases shows that the finitely many `vᵢ * wⱼ` span `V * W`:
   every product expands into their linear combination, and each belongs to the product
   subspace. Thus `V * W` is finite-dimensional (`def-weil-finite-dimensional-subspace`).
3. The `r + s - 1` products `v₁w₁, ..., vᵣw₁, vᵣw₂, ..., vᵣwₛ` have strictly increasing
   valuations `a₁ + b₁ < ... < aᵣ + b₁ < aᵣ + b₂ < ... < aᵣ + bₛ`, by
   `lem-sc-dvr-valuation-arithmetic`. For `r = 1` or `s = 1`, omit the empty segment.
4. A nonzero scalar from `k` is a unit in `R`, since its inverse also lies in `k`.
   It has valuation zero (`def-sc-discrete-valuation-ring`, Tag 00IE). In any nontrivial
   linear relation among these products, discard zero coefficients. The remaining terms
   still have distinct valuations. Add them in decreasing order of valuation, using the
   unequal-order addition formula from `lem-sc-dvr-valuation-arithmetic`: each partial
   sum is nonzero with the least valuation so far. The final sum cannot vanish. Hence
   the products are independent. Extend them to a basis of the finite-dimensional
   product subspace; `def-weil-vector-space-dimension` gives the claimed bound.
-/
theorem finiteDimensional_mul_and_finrank_add_sub_one_le
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (R : Subalgebra k K) [IsDiscreteValuationRing R] [IsFractionRing R K]
    (hres : Function.Bijective ((IsLocalRing.residue R).comp (algebraMap k R)))
    (V W : Submodule k K) [FiniteDimensional k V] [FiniteDimensional k W]
    (hV : V ≠ ⊥) (hW : W ≠ ⊥) :
    FiniteDimensional k (V * W) ∧
      Module.finrank k V + Module.finrank k W - 1 ≤ Module.finrank k (V * W) := by
  sorry

end Submodule
