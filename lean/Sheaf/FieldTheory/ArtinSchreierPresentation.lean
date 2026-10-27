module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.FieldTheory.Normal.Basic

/-!
# Artin–Schreier presentations and the field/product dichotomy

Source: Stacks Project, Fields, Tag 09DY, `lemma-Artin-Schreier`, and Tag 09I7,
`section-Artin-Schreier` (blueprint: lem-sfb-epp-artin-schreier-presentation).

The quotient algebra is Mathlib's `AdjoinRoot (X ^ p - X - C a)`, with its usual
coefficient algebra structure. The forward presentation is explicitly evaluation at `z`.
-/

@[expose] public section

universe u v

open Polynomial

namespace ArtinSchreier

/-- A normal separable degree-`p` extension in characteristic `p` has an Artin–Schreier
presentation, with the quotient isomorphism given by evaluation at the generator.
Source: Stacks Project, Tag 09DY (blueprint: lem-sfb-epp-artin-schreier-presentation).

Proof: By `lem-weil-pbc-finite-galois-fixed-field`, the automorphism group has order `p`
and fixed field `E`. Use `lem-sfb-prime-order-group-cyclic` to choose a generator `σ`.
For the linear operator `N = σ - 1`, characteristic `p` gives `N ^ p = 0`, whereas
`N ^ (p - 1) ≠ 0` by `lem-per-monoid-characters-linear-independent`. Choose `w` with
`y = N ^ (p - 1) w ≠ 0`. Since `N y = 0`, the fixed-field theorem puts `y` in `E`.
Then `z = y⁻¹ N ^ (p - 2) w` satisfies `σ z = z + 1`, including when `p = 2`.
Thus `z` is outside `E`, and `z ^ p - z` is fixed, hence the image of some `a : E`.
The conjugates `z + i`, for `0 ≤ i < p`, are distinct. Evaluation from the quotient
has zero kernel: a degree less than `p` representative cannot vanish at all these roots
unless it is zero. By `lem-weil-pbc-monic-quotient-free`, the quotient and `F` both have
dimension `p`. Evaluation is therefore bijective, and its image `E[z]` is all of `F`. -/
theorem exists_generator_presentation (p : ℕ) (hp : p.Prime)
    (E : Type u) (F : Type v) [Field E] [Field F] [Algebra E F]
    [CharP E p] [CharP F p] [Normal E F] [Algebra.IsSeparable E F]
    (hdegree : Module.finrank E F = p) :
    ∃ (z : F) (a : E), z ∉ Set.range (algebraMap E F) ∧
      z ^ p - z = algebraMap E F a ∧ Algebra.adjoin E ({z} : Set F) = ⊤ ∧
      ∃ e : AdjoinRoot (X ^ p - X - C a) ≃ₐ[E] F,
        ∀ q : E[X], e (AdjoinRoot.mk (X ^ p - X - C a) q) = aeval z q := by
  sorry

/-- An Artin–Schreier quotient is either a normal separable degree-`p` field extension
or the product of `p` copies of the base field; the product case is equivalent to a root
in the base field. `IsField.toField` equips the existing quotient ring with its uniquely
determined field structure in the first alternative.
Source: Stacks Project, Tag 09I7, paragraph before Tag 09DY
(blueprint: lem-sfb-epp-artin-schreier-presentation).

Proof: Choose a root `b` in `AlgebraicClosure E` (`def-weil-algebraic-closure`).
The distinct roots are exactly `b + i` for `0 ≤ i < p`. The derivative of
`f = X ^ p - X - C a` is `-1`, so its minimal-polynomial factors are separable
(`def-pc-separable-polynomial`, `def-weil-pbc-separable-algebraic-extension`).
By `lem-trf-simple-separable-field-extension`, `E(b)/E` is separable. All roots lie in
`E(b)`, so `lem-sfb-splitting-field-finite-normal` gives finite dimensionality and
normality. By `lem-weil-pbc-finite-galois-fixed-field`, its automorphism group has order
its degree. Sending an automorphism to its translation of `b` embeds this group in the
additive prime field. If `b` is not in `E`, a nonzero translation generates `p` distinct
automorphisms. Hence the degree is `p`, and evaluation identifies the quotient with
`E(b)` by the degree/root argument of the forward presentation and the monic basis
`lem-weil-pbc-monic-quotient-free`. If `b = u` lies in `E`, evaluate at the `p` distinct
roots `u + i`. Lagrange interpolation supplies a surjective map to `E ^ p`, and the
root bound on degree less than `p` representatives gives injectivity. A base-field
root means precisely `a = u ^ p - u`. Conversely a product isomorphism followed by
a coordinate projection sends the class of `X` to such a root. The alternatives are
exclusive: `p ≥ 2`, and the product has nonzero zero divisors. -/
theorem quotient_field_or_product (p : ℕ) (hp : p.Prime)
    (E : Type u) [Field E] [CharP E p] (a : E) :
    ((∃ h : IsField (AdjoinRoot (X ^ p - X - C a)),
        @Normal E (AdjoinRoot (X ^ p - X - C a)) _ h.toField _) ∧
      Algebra.IsSeparable E (AdjoinRoot (X ^ p - X - C a)) ∧
      Module.finrank E (AdjoinRoot (X ^ p - X - C a)) = p ∨
      Nonempty (AdjoinRoot (X ^ p - X - C a) ≃ₐ[E] (Fin p → E))) ∧
    (Nonempty (AdjoinRoot (X ^ p - X - C a) ≃ₐ[E] (Fin p → E)) ↔
      ∃ u : E, a = u ^ p - u) := by
  sorry

end ArtinSchreier
