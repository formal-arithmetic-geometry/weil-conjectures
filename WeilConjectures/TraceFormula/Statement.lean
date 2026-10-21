/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite

/-!

# The Grothendieck–Lefschetz trace formula for Weil objects

Let `ℓ` be a prime and `k = 𝔽_q` a finite field of characteristic `p ≠ ℓ`. For a separated
scheme `X` of finite type over `Spec k` with an automorphism `e : X ≅ X` over `Spec k` and a Weil
object `(K, φ_K)` of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` for `e`, the trace formula states that for every `n : ℕ`
```
L_{n+1}(X, K) = ∑_{x̄ ∈ X(𝔽_{q^{n+1}})} t_{n+1}(K; x̄),
```
that is
```
∑ᵢ (-1)ⁱ Tr(Fr_{c,n+1} | Hⁱ_c(X_k̄, K)) = ∑_{x̄} ∑ⱼ (-1)ʲ Tr(Fr_{x̄,n+1} | Hʲ(K)_x̄),
```
with both sides built from the existing Weil functors in
`WeilConjectures.TraceFormula.WeilTrace` (`ProEtale.CondensedRing.weilTraceFormula`). The index
`n` stands for the Frobenius power `n + 1`. The points of degree `n + 1` are the geometric points
`x̄` over the base point with `x̄ ≫ e^{n+1} = σ^{n+1} ≫ x̄`
(`ProEtale.CondensedRing.frobeniusFixedPoints`). No Frobenius correspondence, graph or kernel
object occurs in the hypotheses or in the conclusion.

## The relative form

The trace formula is the case `Y = Spec k` of the compatibility of the Weil lower shriek with the
pushforward of trace functions (`ProEtale.CondensedRing.weilShriekTraceFunction`): for a morphism
`f : X ⟶ Y` over `Spec k`, automorphisms `e_X`, `e_Y` with `e_X ≫ f = f ≫ e_Y` and a point `ȳ` of
`Y` of degree `n + 1`,
```
t_{n+1}(Rf_!^Weil K; ȳ) = ∑_{x̄ ↦ ȳ} t_{n+1}(K; x̄),
```
the sum running over the points of `X` of degree `n + 1` lying over `ȳ`. The absolute formula is
deduced from it: the base `Spec k` has the single point `s` of degree `n + 1`, at which the local
trace of `Ra_!^Weil K` is the global trace by definition.

## The twisting automorphism

For `e = 𝟙` and the classical Weil structure this is the Grothendieck–Lefschetz trace formula
for `X` over `𝔽_q`. For an automorphism `e` of finite order, `σ` twisted by `e` is the Frobenius
of a twisted form of `X` over `𝔽_q`, which has `frobeniusFixedPoints e n` as its set of
`𝔽_{q^{n+1}}`-rational points, and the formula is the trace formula on that form (as in
Deligne–Lusztig). The statements assume `e` has finite order: for an automorphism of infinite
order the twisted Frobenius is no longer the Frobenius of a model over `𝔽_q`.

The geometric Galois Frobenius `g_X` of a geometric fiber is not of this form, since the geometric
fiber is not of finite type over `𝔽_q`
(see `WeilConjectures.WeilObject.BoundedConstructible.Defs`). Once the bounded constructible
Weil formalism is extended to it, the same statements apply with the base `Spec k̄` and the
automorphism `σ` in place of `Spec k` and the identity.

## Main results

- `ProEtale.CondensedRing.weilShriekTraceFunction`: the sheaf–function compatibility of the Weil
  lower shriek, the deep sorried input.
- `ProEtale.CondensedRing.weilTraceFormula`: the trace formula, deduced from the relative form.
- `ProEtale.CondensedRing.weilPointCount`: the point count `L_{n+1}(X, ℚ̲̄_ℓ) = #X(𝔽_{q^{n+1}})`
  for the canonical Weil unit, deduced from the trace formula and the normalization of the local
  trace of the unit.
- `ProEtale.CondensedRing.weilGlobalSupertrace_point_unit`: the normalization test N1, the
  global trace of the unit of the base is `1`.

These are the project's statements of the trace formula. They are stated for the Frobenius of
`Spec k̄` twisted by an automorphism `e` of `X`, with the powers `CategoryTheory.Iso.powSucc e n`
and the iterated Weil structures `ProEtale.CondensedRing.WeilSheaf.powSucc` on homology sheaves.
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

/-- The sheaf–function compatibility of the Weil lower shriek: for a morphism `f : X ⟶ Y` of
separated schemes of finite type over `Spec k`, automorphisms `e_X`, `e_Y` over `Spec k` with
`e_X ≫ f = f ≫ e_Y` and `e_X` of finite order, a Weil object `K` for `e_X` and a point `ȳ` of `Y`
of degree `n + 1`,
```
t_{n+1}(Rf_!^Weil K; ȳ) = ∑_{x̄ ↦ ȳ} t_{n+1}(K; x̄),
```
the sum running over the points `x̄` of `X` of degree `n + 1` with `x̄ ≫ f = ȳ`. By compactly
supported base change of the Weil lower shriek to `ȳ`, this is the trace formula for the fiber of
`f` over `ȳ`.

This is the relative, twisted variant of blueprint `thm-trf-grothendieck-lefschetz-finite-ring`,
which is stated for the model Frobenius. -/
theorem weilShriekTraceFunction {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (eX : X ≅ X) (eY : Y ≅ Y) {f : X ⟶ Y} (hf : eX.hom ≫ f = f ≫ eY.hom)
    (he : ∃ m : ℕ, eX.powSucc m = Iso.refl X)
    (K : WeilBoundedConstructible ℓ eX.hom) (n : ℕ) (y : frobeniusFixedPoints eY n) :
    weilStalkSupertrace ℓ n y.1 y.2.2 ((weilLowerShriek ℓ eX eY hf).obj K) =
      ∑ᶠ x : {x : frobeniusFixedPoints eX n // x.1 ≫ f.left = y.1},
        weilStalkSupertrace ℓ n x.1.1 x.1.2.2 K :=
  sorry

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] (e : X ≅ X)

/-- **The Grothendieck–Lefschetz trace formula for Weil objects.** For a separated scheme `X` of
finite type over `𝔽_q`, an automorphism `e` of `X` over `𝔽_q` of finite order and a Weil object
`K` of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` for `e`, for every `n : ℕ`,
```
∑ᵢ (-1)ⁱ Tr(Fr_{c,n+1} | Hⁱ_c(X_k̄, K))
  = ∑_{x̄ ∈ X(𝔽_{q^{n+1}})} ∑ⱼ (-1)ʲ Tr(Fr_{x̄,n+1} | Hʲ(K)_x̄).
```
It is the case `Y = Spec k` of `weilShriekTraceFunction`. This is a variant of blueprint
`thm-trf-grothendieck-lefschetz-finite-ring` for the Frobenius twisted by `e`. -/
theorem weilTraceFormula (he : ∃ m : ℕ, e.powSucc m = Iso.refl X)
    (K : WeilBoundedConstructible ℓ e.hom) (n : ℕ) :
    weilGlobalSupertrace ℓ e K n =
      ∑ᶠ x : frobeniusFixedPoints e n, weilStalkSupertrace ℓ n x.1 x.2.2 K := by
  refine (weilShriekTraceFunction ℓ e (Iso.refl (point k)) (f := toPoint X) (toPoint_ext _ _) he K n
    (pointFixedPoint n)).trans ?_
  exact finsum_comp_equiv (Equiv.subtypeUnivEquiv fun x ↦ x.2.1)
    (f := fun x : frobeniusFixedPoints e n ↦ weilStalkSupertrace ℓ n x.1 x.2.2 K)

/-- **Point counting.** For the canonical Weil unit `ℚ̲̄_ℓ,X`, the global trace in degree `n + 1` is
the number of points of degree `n + 1`, that is `#X(𝔽_{q^{n+1}})` for `e = 𝟙`:
```
∑ᵢ (-1)ⁱ Tr(Fr_{c,n+1} | Hⁱ_c(X_k̄, ℚ̄_ℓ)) = #X(𝔽_{q^{n+1}}).
```
This is a variant of blueprint `cor-trf-point-counting` for the Frobenius twisted by `e`. -/
theorem weilPointCount (he : ∃ m : ℕ, e.powSucc m = Iso.refl X) (n : ℕ) :
    weilGlobalSupertrace ℓ e (WeilBoundedConstructible.unit ℓ e.hom) n =
      (Nat.card (frobeniusFixedPoints e n) : _) := by
  rw [weilTraceFormula ℓ e he]
  simp only [weilStalkSupertrace_unit]
  have := finite_frobeniusFixedPoints_of_powSucc_eq_refl e he n
  let := Fintype.ofFinite (frobeniusFixedPoints e n)
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card,
    nsmul_eq_mul, mul_one]

/-- The normalization test N1: the canonical Weil unit of the base `Spec 𝔽_q` has global trace
`1` in every degree. -/
theorem weilGlobalSupertrace_point_unit (n : ℕ) :
    weilGlobalSupertrace ℓ (Iso.refl (point k))
      (WeilBoundedConstructible.unit ℓ (Iso.refl (point k)).hom) n = 1 := by
  rw [weilPointCount ℓ (Iso.refl (point k)) ⟨0, rfl⟩, Nat.card_unique, Nat.cast_one]

end AlgebraicGeometry.ProEtale.CondensedRing
