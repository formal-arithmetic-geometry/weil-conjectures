module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Higher adic graded modules

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose III, section 4,
printed p.39 (blueprint: def-per-higher-adic-graded).

The operations are given as functions, without selecting ring or module law proofs.
They use quotient representatives and finite sums. The representatives are chosen by
`Quotient.out`, whose correctness is already proved in Lean; no postponed existence
assertion supplies any data. The total class function is zero off its filtration step.
On filtered representatives these are precisely the usual product and scalar action.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped DirectSum

namespace Ideal

variable {B : Type u} [CommRing B]

/-- The integer adic filtration, extended by the whole module in nonpositive degrees.
Source: ILO, Expose III, section 4, p.39 (blueprint: def-per-higher-adic-graded). -/
def intAdicPower (I : Ideal B) (V : Type v) [AddCommGroup V] [Module B V]
    (q : ℤ) : Submodule B V :=
  I ^ q.toNat • (⊤ : Submodule B V)

/-- The degree `q` piece `I^q V / I^(q+a) V` of the higher graded module.
Source: ILO, Expose III, section 4, p.39 (blueprint: def-per-higher-adic-graded). -/
abbrev higherAdicPiece (I : Ideal B) (V : Type v) [AddCommGroup V] [Module B V]
    (a : ℕ) (q : ℤ) : Type v :=
  intAdicPower I V q ⧸
    (intAdicPower I V (q + a)).comap (intAdicPower I V q).subtype

/-- The integer-graded direct sum `G_a(V)` of the higher adic pieces.
Source: ILO, Expose III, section 4, p.39 (blueprint: def-per-higher-adic-graded). -/
abbrev higherAdicGraded (I : Ideal B) (V : Type v) [AddCommGroup V] [Module B V]
    (a : ℕ) : Type v :=
  ⨁ q : ℤ, higherAdicPiece I V a q

/-- The homogeneous class of `x` in degree `q`, extended by zero when `x` is
outside `I^q V`. All normalization statements restrict to filtered representatives.
Source: ILO, Expose III, section 4, p.39 (blueprint: def-per-higher-adic-graded). -/
noncomputable def higherAdicClass (I : Ideal B) (V : Type v)
    [AddCommGroup V] [Module B V] (a : ℕ) (q : ℤ) (x : V) :
    higherAdicGraded I V a := by
  classical
  exact if hx : x ∈ intAdicPower I V q then
    DirectSum.lof B ℤ (higherAdicPiece I V a) q (Submodule.Quotient.mk ⟨x, hx⟩)
  else 0

/-- The action of `G_a(B)` on `G_a(V)`: sum the homogeneous classes of `b_s x_q`.
Each representative lies in the indicated filtration step; changing a representative
changes the product by `I^(s+q+a)V`. Source: ILO, Expose III, section 4, p.39
(blueprint: def-per-higher-adic-graded). -/
noncomputable def higherAdicAction (I : Ideal B) (V : Type v)
    [AddCommGroup V] [Module B V] (a : ℕ)
    (b : higherAdicGraded I B a) (x : higherAdicGraded I V a) :
    higherAdicGraded I V a := by
  classical
  exact ∑ s ∈ b.support, ∑ q ∈ x.support,
    higherAdicClass I V a (s + q) ((b s).out.1 • (x q).out.1)

/-- Multiplication on `G_a(B/U)` for the ideal `U` (an ideal is a submodule of `B`).
Lift homogeneous classes first to `B/U`, then to `B`, multiply, and take the
class in total degree. This is independent of both choices of lifts, since `U`
is an ideal and the denominator is `I^(s+q+a)`.
Source: ILO, Expose III, section 4 and Proposition 4.5(iv), pp.39--40
(blueprint: def-per-higher-adic-graded). -/
noncomputable def higherAdicQuotientMul (I : Ideal B) (U : Submodule B B) (a : ℕ)
    (x y : higherAdicGraded I (B ⧸ U) a) : higherAdicGraded I (B ⧸ U) a := by
  classical
  exact ∑ s ∈ x.support, ∑ q ∈ y.support,
    higherAdicClass I (B ⧸ U) a (s + q)
      (U.mkQ ((x s).out.1.out * (y q).out.1.out))

/-- The unit of `G_a(B/U)` is the degree-zero class of `1`.
Source: ILO, Expose III, section 4 and Proposition 4.5(iv), pp.39--40
(blueprint: def-per-higher-adic-graded). -/
noncomputable def higherAdicQuotientOne (I : Ideal B) (U : Submodule B B) (a : ℕ) :
    higherAdicGraded I (B ⧸ U) a :=
  higherAdicClass I (B ⧸ U) a 0 (U.mkQ 1)

end Ideal
