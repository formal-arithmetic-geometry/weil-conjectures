/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Finiteness.Ideal
public import WeilConjectures.Blowup.Affine.Defs

/-!
# Clearing a fractional inverse on a blowup chart

Source: ILO, Travaux de Gabber, Expose XX, section 4.4, printed p.373;
Stacks Project, algebra.tex, Tag 07Z3, and divisors.tex, Tags 0804 and 02OS.
(blueprint: lem-per-blowup-domination-colon-power)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.AffineBlowup

/-- Domination supplies a positive-power colon relation for each chart denominator.

Source: the chart and denominator argument in steps 1--4 of
`lem-per-blowup-domination-ideal-factorization`, expanding the criterion in
ILO, Travaux de Gabber, Expose XX, section 4.4, printed p.373. The chart fraction
calculation is Stacks Project, algebra.tex, Tag 07Z3, with the chart cover and
principalization in divisors.tex, Tags 0804 and 02OS. Evaluation for an invertible
module is more-algebra.tex, Tag 0B8I.
(blueprint: lem-per-blowup-domination-colon-power)

Proof: fix `b ∈ K` and put `A = R[K/b] ⊆ R[1/b]`. Its elements are `c/b^d`
with `c ∈ K^d`; multiplication by `b` is injective on `A`. On the target blowup,
`J` is locally principal. Pulling back its local generators along `f` shows
that `J A` is locally principal. Choose `a ≥ 1` with `b^a ∈ J`, using
`K ≤ J.radical`. Every local generator `v` of `J A` divides `b^a`, so is
regular: `v x = 0` implies `b^a x = 0`, and thus `x = 0`. Hence the ideal
sheaf with affine sections `J A` is an invertible module.

Affine evaluation produces finitely many `x_ν ∈ J A` and linear maps
`φ_ν : J A → A` with `∑ φ_ν(x_ν) = 1`. In `R[1/b]` set
`z_ν = φ_ν(b^a)/b^a`. Linearity gives `φ_ν(x) = x z_ν` for `x ∈ J A`.
For a fixed finite generating family `j_t` of `J`, write
`x_ν = ∑ j_t q_{tν}` and put `w_t = ∑ q_{tν} z_ν`. Then
`∑ j_t w_t = 1` and each `j_s w_t` belongs to `A`.

Choose a common `e ≥ 1` so that `w_t = c_t/b^e`, with `c_t ∈ R`,
and `j_s w_t = v_{st}/b^e`, with `v_{st} ∈ K^e`. Increasing denominators
preserves this last membership because `b ∈ K`. The equalities
`j_s c_t = v_{st}` and `∑ j_t c_t = b^e` hold in `R[1/b]`.
Multiply them all by one power `b^v` so that they hold in `R`.
Then `c'_t = b^v c_t` satisfies `J c'_t ⊆ K^(e+v)` and
`∑ j_t c'_t = b^(e+v)`. Thus `b^(e+v) ∈ J (K^(e+v) : J)`.
This argument permits zero rings and nilpotent denominators: the chart can
be empty, and localization equalities still clear by a finite power.
-/
theorem exists_pow_mem_mul_colon_of_hom
    {R : Type u} [CommRing R] (J K : Ideal R) (hJ : J.FG)
    (hKJ : K ≤ J.radical)
    (f : AffineBlowup K ⟶ AffineBlowup J) (hf : f ≫ toSpec J = toSpec K) :
    ∀ b ∈ K, ∃ e : ℕ, 1 ≤ e ∧ b ^ e ∈ J * (K ^ e).colon (J : Set R) := by sorry

end AlgebraicGeometry.AffineBlowup
