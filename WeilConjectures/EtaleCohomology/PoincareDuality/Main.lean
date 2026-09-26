/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius
public import WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup

/-!

# Poincaré duality

Let `X₀` be smooth, proper and geometrically connected of pure dimension `d` over the finite
field `k₀` with `q` elements, let `X = X₀ ×_{k₀} k` be its base change to an algebraic closure
and let `Λ` be a field coefficient stage. With `K_X = Λ_X` the constant sheaf carrying its
canonical Weil structure, `F` the geometric Frobenius on the `H^i(X, Λ)` and `⟨-,-⟩_i` the
trace–cup pairing with values in `Λ(-d)`:

1. **Trace.** `tr_X : H^{2d}(X, Λ) ⟶ Λ(-d)` is an isomorphism.
2. **Finiteness.** `H^i(X, Λ)` is finite over `Λ` for all `i`, and vanishes outside `[0, 2d]`.
3. **Pairing.** `⟨-,-⟩_i : H^i(X, Λ) ⊗ H^j(X, Λ) ⟶ Λ(-d)` is perfect for `i + j = 2d`, and is
   graded commutative: `⟨y, x⟩_j = (-1)^i ⟨x, y⟩_i`.
4. **Frobenius similitude.** `⟨F x, F y⟩_i = q^d ⟨x, y⟩_i`.
5. **Reciprocity.** The adjoint of the pairing identifies `H^j(X, Λ)` with the dual of
   `H^i(X, Λ)` twisted by `-d`, intertwining `F` with `q^d (F^{-1})^t`; the eigenvalues of `F`
   on `H^j(X, Λ)` are therefore the `q^d / α` for the eigenvalues `α` of `F` on `H^i(X, Λ)`,
   with multiplicity (`LinearMap.charpoly_roots_of_similitude`).
6. **Base change.** For a finite extension of degree `r` of `k₀` inside `k` the geometric
   Frobenius is `F^r`, the pairings stay perfect and `⟨F^r x, F^r y⟩_i = (q^r)^d ⟨x, y⟩_i`.

## Main results

- `AlgebraicGeometry.ProEtale.poincare_duality`.

-/

@[expose] public section

universe u

open CategoryTheory Abelian Limits MonoidalCategory Opposite

namespace AlgebraicGeometry

open Scheme ProEtale

namespace ProEtale

variable {Λ : Type (u + 1)} [Field Λ] {k₀ : Type u} [Field k₀] [Finite k₀] {d : ℕ}

/-- Blueprint `sk-thm-poincare-duality`: Poincaré duality.

For `X₀` smooth, proper and geometrically connected of pure dimension `d` over the finite
field `k₀` with `q` elements, with geometric fibre `X` and field coefficients `Λ`: the trace is
an isomorphism, the cohomology is finite and concentrated in `[0, 2d]`, the trace–cup pairing
is perfect and graded commutative, the geometric Frobenius is a similitude of factor `q^d`,
the pairing identifies `H^j` with the `(-d)`-twisted dual of `H^i` intertwining `F` with
`q^d (F^{-1})^t`, and all of this stays true for the `r`-th power of `F`, the geometric
Frobenius of the degree `r` extension of `k₀`. -/
theorem poincare_duality (T : PoincareDualitySetting k₀ d)
    [IsProper T.modelStructureMorphism]
    (k : Type u) [Field k] [IsAlgClosed k] [Algebra k₀ k] [Algebra.IsAlgebraic k₀ k]
    [HasCompactification (T.structureMorphism k)]
    (γ : ((tateTwist (ModuleCat.{u + 1} Λ) (T.geometricFibre k) (d : ℤ)).obj
        (𝟙_ _))⟦(2 * d : ℤ)⟧ ≅
      dualizingComplex (ModuleCat.{u + 1} Λ) (T.structureMorphism k)) :
    -- (1) the trace is an isomorphism
    IsIso (traceMap (ModuleCat.{u + 1} Λ) (T.structureMorphism k) d γ) ∧
    -- (2) finiteness and vanishing outside `[0, 2d]`
    (∀ i : ℤ, Module.Finite Λ
        ((cohomology (ModuleCat.{u + 1} Λ) (T.geometricFibre k) i).obj (𝟙_ _))) ∧
    (∀ i : ℤ, i < 0 ∨ (2 * d : ℤ) < i →
      IsZero ((cohomology (ModuleCat.{u + 1} Λ) (T.geometricFibre k) i).obj (𝟙_ _))) ∧
    (∀ i j : ℕ, ∀ hij : i + j = 2 * d,
      -- (3) the trace–cup pairing is perfect and graded commutative
      MonoidalClosed.IsPerfectPairing
        (traceCupPairing (ModuleCat.{u + 1} Λ) (T.structureMorphism k) d γ i j hij) ∧
      (β_ _ _).hom ≫
          traceCupPairing (ModuleCat.{u + 1} Λ) (T.structureMorphism k) d γ j i (by omega) =
        ((-1 : ℤ) ^ i) •
          traceCupPairing (ModuleCat.{u + 1} Λ) (T.structureMorphism k) d γ i j hij ∧
      -- (4) Frobenius is a similitude of factor `q^d`
      tensorHom
          ((WeilComplex.unit (ModuleCat.{u + 1} Λ) (T.geometricFrobenius k)).cohomologyFrobenius
            (i : ℤ))
          ((WeilComplex.unit (ModuleCat.{u + 1} Λ) (T.geometricFrobenius k)).cohomologyFrobenius
            (j : ℤ)) ≫
          traceCupPairing (ModuleCat.{u + 1} Λ) (T.structureMorphism k) d γ i j hij =
        ((Nat.card k₀ ^ d : ℤ)) •
          traceCupPairing (ModuleCat.{u + 1} Λ) (T.structureMorphism k) d γ i j hij ∧
      -- (5) reciprocity: `F` on `H^j` is `q^d` times the transpose inverse of `F` on `H^i`
      (WeilComplex.unit (ModuleCat.{u + 1} Λ) (T.geometricFrobenius k)).cohomologyFrobenius
            (j : ℤ) ≫
          MonoidalClosed.curry
            (traceCupPairing (ModuleCat.{u + 1} Λ) (T.structureMorphism k) d γ i j hij) ≫
          (MonoidalClosed.pre
            ((WeilComplex.unit (ModuleCat.{u + 1} Λ)
              (T.geometricFrobenius k)).cohomologyFrobenius (i : ℤ))).app _ =
        ((Nat.card k₀ ^ d : ℤ)) • MonoidalClosed.curry
          (traceCupPairing (ModuleCat.{u + 1} Λ) (T.structureMorphism k) d γ i j hij) ∧
      -- (6) base change to the degree `r` extension of `k₀`
      ∀ r : ℕ, tensorHom
          ((WeilComplex.unit (ModuleCat.{u + 1} Λ)
            (T.geometricFrobenius k)).cohomologyFrobeniusPow (i : ℤ) r)
          ((WeilComplex.unit (ModuleCat.{u + 1} Λ)
            (T.geometricFrobenius k)).cohomologyFrobeniusPow (j : ℤ) r) ≫
          traceCupPairing (ModuleCat.{u + 1} Λ) (T.structureMorphism k) d γ i j hij =
        (((Nat.card k₀ ^ r) ^ d : ℤ)) •
          traceCupPairing (ModuleCat.{u + 1} Λ) (T.structureMorphism k) d γ i j hij) :=
  sorry

end ProEtale

end AlgebraicGeometry
