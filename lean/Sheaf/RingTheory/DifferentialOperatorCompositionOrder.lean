module

public import Sheaf.RingTheory.DifferentialOperatorOrder

/-!
# Composition adds differential order bounds

Source: Stacks Project, algebra.tex, Tag 09CJ, lemma-composition-differential-operators.
(blueprint: lem-trf-differential-operator-composition-order)
-/

@[expose] public section

universe u v w₁ w₂ w₃

namespace LinearMap

/-- Composing differential operators of orders at most `k` and `l` gives order at most `k + l`.
Source: Stacks Project, algebra.tex, Tag 09CJ, lemma-composition-differential-operators.
(blueprint: lem-trf-differential-operator-composition-order)

Proof: scalar multiplication is `R`-linear because the scalars act through the commutative
algebra `C`. Induction on the bound shows that zero and sums preserve each order bound:
at zero use `C`-linearity, and at successor order use that the scalar commutator preserves
zero and sums. Now use strong induction on `k + l`, for all bounds and all module triples.
If the sum is zero both maps are `C`-linear, as is their composite. Otherwise, additivity
of `E` gives the identity
`[E.comp D, c] = E.comp [D, c] + [E, c].comp D`.
When `k > 0`, the first commutator has order at most `k - 1`, so induction bounds its
composite by `k + l - 1`; when `k = 0`, this summand is zero by `C`-linearity of `D`.
Likewise, the second summand is bounded by induction if `l > 0`, and is zero if `l = 0`.
Closure under sums bounds the displayed commutator by `k + l - 1` for every `c`.
The recursive definition therefore bounds the composite by `k + l`. -/
theorem IsDifferentialOperatorOfOrderLE.comp
    {R : Type u} {C : Type v} [CommRing R] [CommRing C] [Algebra R C]
    {L : Type w₁} {M : Type w₂} {N : Type w₃}
    [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
    [Module C L] [Module C M] [Module C N] [Module R L] [Module R M] [Module R N]
    [IsScalarTower R C L] [IsScalarTower R C M] [IsScalarTower R C N]
    {k l : ℕ} {D : L →ₗ[R] M} {E : M →ₗ[R] N}
    (hD : IsDifferentialOperatorOfOrderLE R C k D)
    (hE : IsDifferentialOperatorOfOrderLE R C l E) :
    IsDifferentialOperatorOfOrderLE R C (k + l) (E.comp D) := sorry

end LinearMap
