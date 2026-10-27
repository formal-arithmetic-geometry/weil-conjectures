module

public import Sheaf.FieldTheory.PerfectCore
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.PurelyInseparable.Exponent

/-!
# Perfect cores under finite field extensions

Source: ILO, Travaux de Gabber, Exposé IV, Lemma 3.2.2 and Proposition 3.2.3(ii),
printed p. 56 (blueprint: lem-per-finite-extension-perfect-core).
-/

@[expose] public section

universe u v

namespace Field

/-- Every element of the perfect core of a finite extension is algebraic over the
perfect core of the base, with no separability assumption.

Source: ILO, Travaux de Gabber, Exposé IV, Lemma 3.2.2 and Proposition 3.2.3(ii),
printed p. 56 (blueprint: lem-per-finite-extension-perfect-core).

Proof: Finite dimensionality gives algebraicity by linear dependence of powers.
Let `S` be the relative separable closure of `K` in `L`
(`def-weil-pbc-relative-separable-closure`). Then `S/K` is separable algebraic and
`L/S` is purely inseparable (`lem-weil-pbc-separable-first-purely-inseparable`).
The finite spanning family over `K` also spans over `S`, so the latter extension
has a uniform exponent `e` (`lem-per-finite-extension-separable-core-bounded-exponent`).
For `x` in the perfect core of `L`, choose for each `n` an element `y` with
`y ^ (p ^ (n + e)) = x`. Then `z = y ^ (p ^ e)` lies in `S` and
`z ^ (p ^ n) = x`. In particular `x` lies in the perfect core of `S`.
Embed `S` into a separable closure of `K` (`def-pd-separable-closure` and
`lem-weil-pbc-separable-extension-embeds-separably-closed`); the embedding carries
these roots to roots, so its image of `x` lies in that closure's perfect core.
By `lem-per-separable-closure-perfect-core` (ILO Lemma 3.2.2), this image satisfies
a nonzero polynomial over the perfect core of `K`. The embedding fixes the
coefficients; its injectivity pulls this polynomial relation back to `S`, hence to `L`.
-/
theorem isAlgebraic_of_mem_perfectCore_of_finiteDimensional
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (p : ℕ) [Fact p.Prime] [CharP K p] [CharP L p] [FiniteDimensional K L]
    (x : L) (hx : x ∈ perfectCore L p) :
    ∃ P : Polynomial (perfectCore K p), P ≠ 0 ∧
      P.eval₂ ((algebraMap K L).comp (perfectCore K p).subtype) x = 0 := by
  sorry

end Field
