module

public import Sheaf.CategoryTheory.DgPropertyPFiltration
import Sheaf.Paper.DerivedTotalResolutionQuasiIso

/-!
# Property-(P) resolutions of right DG modules

Source: Stacks Project, dga.tex, Tag 09KP, lemma-resolve, using Tag 09KN,
lemma-good-quotient (blueprint: lem-sfb-dg-property-p-resolution).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace CategoryTheory.DgAlgebra

/-- Every right DG module over an arbitrary associative unital DG algebra admits
an unrestricted property-(P) resolution which is also degreewise surjective.
All component groups and all free-layer index sets lie in the same universe `u`.
Source: Stacks Project, dga.tex, Tag 09KP, lemma-resolve, and its proof
(blueprint: lem-sfb-dg-property-p-resolution).

Proof:
1. Starting with M₀ = M, repeatedly apply lem-sfb-dg-two-layer-free-cover to obtain
   surjections πᵢ : Qᵢ → Mᵢ, surjective also on cocycles, and set Mᵢ₊₁ = ker πᵢ.
   The composites fᵢ₊₁ : Qᵢ₊₁ → Mᵢ₊₁ → Qᵢ give an augmented chain exact in each degree.
2. The chain is also exact on cocycles: a cycle killed by the next map belongs to
   the kernel DG submodule, and lifts to a cycle under the next πᵢ. At the end use
   surjectivity of π₀ on cocycles. Consecutive composites vanish by construction.
3. Take Pⁿ = ⨁ i ≥ 0, Qᵢⁿ⁺ⁱ, with unchanged right action and differential
   D(x) = fᵢ(x) + (-1)ⁱ d(x) on Qᵢ. The mixed terms cancel in D², and the action
   satisfies Leibniz since (-1)ⁱ⁺ᵇ = (-1)ᵇ⁻ⁱ for x of internal degree b.
   Define q by π₀ on Q₀ and zero elsewhere. It commutes with D and is surjective.
4. Forgetting the DG action, apply lem-pc-derived-total-resolution-quasi-iso over ℤ
   to the degreewise and cocyclewise exact chain. Its total differential is D,
   so q induces isomorphisms on every cohomology group.
5. Give the closed free generators of Qᵢ height 2i and its other free generators
   height 2i+1. Let Fₙ be their graded span at heights less than n. D strictly
   lowers generator height, so these are DG submodules and F₀ = 0. Finite support
   proves exhaustiveness. Coordinate deletion gives graded right-linear retractions.
   The quotient generators are closed and their differentials on coefficients have
   sign (-1)ᵗ⁻ⁱ, giving shifts A[i-t] for generators of internal degree t.
6. Kernels, countable unions and finite-support sums preserve the component universe,
   so P and every layer index set remain u-small. No boundedness, commutativity or
   countability hypothesis was used. For M = 0 one can take P = 0 and empty layers. -/
theorem exists_propertyP_resolution (A : Algebra.{u}) (M : RightModule A) :
    ∃ (P : RightModule A) (q : P ⟶ M), HasPropertyP A P ∧
      quasiIsomorphisms A q ∧
      ∀ n : ℤ, Function.Surjective (((underlying A).map q).f n) := by
  sorry

end CategoryTheory.DgAlgebra
