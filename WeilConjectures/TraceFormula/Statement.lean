/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.TraceFormula.ShriekTraceFunctionBaseCases

/-!

# The Grothendieck–Lefschetz trace formula for Weil objects

Let `ℓ` be a prime and `k = 𝔽_q` a finite field of characteristic `p ≠ ℓ`. For a separated
scheme `X` of finite type over `Spec k` with an automorphism `e : X ≅ X` over `Spec k` and a Weil
object `(K, φ_K)` of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` for `e`, the trace formula states that for every `n ≠ 0`
```
Lₙ(X, K) = ∑_{x̄ ∈ X(𝔽_{qⁿ})} tₙ(K; x̄),
```
that is
```
∑ᵢ (-1)ⁱ Tr(Fr_{c,n} | Hⁱ_c(X_k̄, K)) = ∑_{x̄} ∑ⱼ (-1)ʲ Tr(Fr_{x̄,n} | Hʲ(K)_x̄),
```
with both sides built from the existing Weil functors in
`WeilConjectures.TraceFormula.WeilTrace` (`ProEtale.CondensedRing.weilTraceFormula`). The index
`n` is the Frobenius power. The points of degree `n` are the geometric points `x̄` over the base
point with `x̄ ≫ eⁿ = σⁿ ≫ x̄` (`ProEtale.CondensedRing.frobeniusFixedPoints`). For `n = 0` every
geometric point over the base point qualifies, so the statements assume `[NeZero n]`. No Frobenius
correspondence, graph or kernel object occurs in the hypotheses or in the conclusion.

## The relative form

The trace formula is the case `Y = Spec k` of the compatibility of the Weil lower shriek with the
pushforward of trace functions (`ProEtale.CondensedRing.weilShriekTraceFunction`): for a morphism
`f : X ⟶ Y` over `Spec k`, automorphisms `e_X`, `e_Y` with `e_X ≫ f = f ≫ e_Y` and a point `ȳ` of
`Y` of degree `n ≠ 0`,
```
tₙ(Rf_!^Weil K; ȳ) = ∑_{x̄ ↦ ȳ} tₙ(K; x̄),
```
the sum running over the points of `X` of degree `n` lying over `ȳ`. The absolute formula is
deduced from it: the base `Spec k` has the single point `s` of degree `n`, at which the local
trace of `Ra_!^Weil K` is the global trace by definition.

## The twisting automorphism

For `e = 𝟙` and the classical Weil structure this is the Grothendieck–Lefschetz trace formula
for `X` over `𝔽_q`. For an automorphism `e` of finite order, `σ` twisted by `e` is the Frobenius
of a twisted form of `X` over `𝔽_q`, which has `frobeniusFixedPoints e n` as its set of
`𝔽_{qⁿ}`-rational points, and the formula is the trace formula on that form (as in
Deligne–Lusztig). The statements assume `e` has finite order, that is `eᵐ = 𝟙` for some `m > 0`:
for an automorphism of infinite order the twisted Frobenius is no longer the Frobenius of a model
over `𝔽_q`.

The geometric Galois Frobenius `g_X` of a geometric fiber is not of this form, since the geometric
fiber is not of finite type over `𝔽_q`
(see `WeilConjectures.WeilObject.BoundedConstructible.Defs`). Once the bounded constructible
Weil formalism is extended to it, the same statements apply with the base `Spec k̄` and the
automorphism `σ` in place of `Spec k` and the identity.

## Main results

- `ProEtale.CondensedRing.weilShriekTraceFunction`: the sheaf–function compatibility of the Weil
  lower shriek, deduced by Noetherian induction
  (`ProEtale.CondensedRing.weilShriekTraceFunction_of_genericallyHolds`) from the base cases of
  `WeilConjectures.TraceFormula.ShriekTraceFunctionBaseCases`.
- `ProEtale.CondensedRing.weilTraceFormula`: the trace formula, deduced from the relative form.
- `ProEtale.CondensedRing.weilPointCount`: the point count `Lₙ(X, ℚ̲̄_ℓ) = #X(𝔽_{qⁿ})` for the
  canonical Weil unit, deduced from the trace formula and the normalization of the local trace of
  the unit.
- `ProEtale.CondensedRing.weilStalkTraceAlternatingSum_weilCompactSupportCohomology_refl_weilUnit`:
  the normalization test N1, the global trace of the unit of the base is `1`.

The sums over points are finite sums, for the `Fintype` structure
`ProEtale.CondensedRing.fintypeFrobeniusFixedPoints`, a local instance in this file.

These are the project's statements of the trace formula. They are stated for the Frobenius of
`Spec k̄` twisted by an automorphism `e` of `X`, with the powers `CategoryTheory.Iso.pow e n` and
the iterated Weil structures `ProEtale.CondensedRing.WeilSheaf.pow` on homology sheaves.
`WeilConjectures.TraceFormula.Main` collects results for the model-Frobenius setting of the
blueprint (an endomorphism `Φ` of `X` with its iterates
`ProEtale.CondensedRing.frobeniusIterate Φ m` and the iterated Weil structures
`ProEtale.CondensedRing.WeilBoundedConstructible.iterateStr`), such as additivity of the trace
along an open subscheme and its closed complement.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Endofunctor

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Finite k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

attribute [local instance] fintypeFrobeniusFixedPoints

open Classical in
/-- The sheaf–function compatibility of the Weil lower shriek: for a morphism `f : X ⟶ Y` of
separated schemes of finite type over `Spec k`, automorphisms `e_X`, `e_Y` over `Spec k` with
`e_X ≫ f = f ≫ e_Y` and `e_X` of finite order, a Weil object `K` for `e_X` and a point `ȳ` of `Y`
of degree `n ≠ 0`,
```
tₙ(Rf_!^Weil K; ȳ) = ∑_{x̄ ↦ ȳ} tₙ(K; x̄),
```
the sum running over the points `x̄` of `X` of degree `n` with `x̄ ≫ f = ȳ`. By compactly
supported base change of the Weil lower shriek to `ȳ`, this is the trace formula for the fiber of
`f` over `ȳ`.

This is the relative, twisted variant of blueprint `thm-trf-grothendieck-lefschetz-finite-ring`,
which is stated for the model Frobenius. -/
theorem weilShriekTraceFunction {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (eX : X ≅ X) (eY : Y ≅ Y) {f : X ⟶ Y} (hf : eX.hom ≫ f = f ≫ eY.hom)
    (he : ∃ m > 0, eX.pow m = Iso.refl X)
    (K : WeilBoundedConstructible ℓ eX.hom) (n : ℕ) [NeZero n] (y : frobeniusFixedPoints eY n) :
    weilStalkTraceAlternatingSum ℓ n y.1 y.2.2 ((weilLowerShriek ℓ eX eY hf).obj K) =
      ∑ x : {x : frobeniusFixedPoints eX n // x.1 ≫ f.left = y.1},
        weilStalkTraceAlternatingSum ℓ n x.1.1 x.1.2.2 K := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne n)
  obtain ⟨p, hp, hpe⟩ := he
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hp.ne'
  rw [weilShriekTraceFunction_of_genericallyHolds ℓ (shriekTraceFunctionGenericallyHolds ℓ k) eX eY
    hf ⟨p, hpe⟩ K m y, finsum_eq_sum_of_fintype]

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] (e : X ≅ X)

open Classical in
/-- **The Grothendieck–Lefschetz trace formula for Weil objects.** For a separated scheme `X` of
finite type over `𝔽_q`, an automorphism `e` of `X` over `𝔽_q` of finite order and a Weil object
`K` of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` for `e`, for every `n ≠ 0`,
```
∑ᵢ (-1)ⁱ Tr(Fr_{c,n} | Hⁱ_c(X_k̄, K)) = ∑_{x̄ ∈ X(𝔽_{qⁿ})} ∑ⱼ (-1)ʲ Tr(Fr_{x̄,n} | Hʲ(K)_x̄),
```
the left side being the local trace of `RΓ_c(X, K)` at the geometric point `s` of the base. It is
the case `Y = Spec k` of `weilShriekTraceFunction`. This is a variant of blueprint
`thm-trf-grothendieck-lefschetz-finite-ring` for the Frobenius twisted by `e`. -/
theorem weilTraceFormula (he : ∃ m > 0, e.pow m = Iso.refl X)
    (K : WeilBoundedConstructible ℓ e.hom) (n : ℕ) [NeZero n] :
    weilStalkTraceAlternatingSum ℓ n (specAlgebraicClosure k) (specAlgebraicClosure_comp_pow n)
        ((weilCompactSupportCohomology ℓ e).obj K) =
      ∑ x : frobeniusFixedPoints e n, weilStalkTraceAlternatingSum ℓ n x.1 x.2.2 K :=
  (weilShriekTraceFunction ℓ e (Iso.refl (point k)) (f := toPoint X) (toPoint_ext _ _) he K n
    default).trans
      (Fintype.sum_equiv (Equiv.subtypeUnivEquiv fun x ↦ by rw [toPoint_left]; exact x.2.1) _ _
        fun _ ↦ rfl)

end AlgebraicGeometry.ProEtale.CondensedRing
