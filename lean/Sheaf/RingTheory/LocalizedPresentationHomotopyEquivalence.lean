/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.Smooth.Basic

/-!
# Homotopy equivalence for localized polynomial presentations

Source: Stacks Project, Algebra, Tags 00S1 and 04EG
(blueprint: lem-trf-localized-presentation-homotopy-equivalence).
-/

@[expose] public section

universe u v w w' i j

open TensorProduct

namespace Algebra.Extension

/-- A polynomial presentation and a localized polynomial presentation of the same algebra
have homotopy equivalent conormal-differential complexes. Source: Stacks Project, Algebra,
Tag 00S1, proof of (4), extended using the square-zero lifting in Tag 04EG
(blueprint: lem-trf-localized-presentation-homotopy-equivalence).

`R` and `P` encode the two surjections to `B`; `eR` identifies the first ring with `A[V]`.
The algebra structure on `P.Ring` identifies it as a localization of `A[E]` at `W`,
compatibly with its `A`-algebra structure. There are no restrictions on the variable sets.
`CotangentSpace` uses `B ⊗ Ω`, the canonical flip of the displayed `Ω ⊗ B` in the node.
The differential is Mathlib's `cotangentComplex`, sending `[h]` to `1 ⊗ dh`.
`Hom` means an `A`-algebra map over `B`, and its canonical `Cotangent.map` and
`CotangentSpace.map` send `[h]` to `[a(h)]` and `b ⊗ dr` to `b ⊗ d(a(r))`.
The lift `ell` has target `R.infinitesimal`, whose ring is exactly `R.Ring / ker²`.
The formula on every quotient representative uniquely specifies the descended derivation
`dbar` as an `A`-linear map; its Leibniz rule follows from the same formula and surjectivity
of the quotient map. The conormal formula is expressed using the injective canonical map
`cotangentToQuotientSquare`, so no representative of `ell(h)` is chosen.
The last four equations are precisely the two degreewise chain homotopies, with sign
`g N(a) - id` and `N(a) g - id`. No map `P.Ring → R.Ring` is required.

Proof for stage 3:
1. Lift the images of the variables `V` through `P → B` and use the universal property
of def-weil-pbc-mv-polynomial-ring to obtain `a`. The maps and chain equation are supplied
by lem-trf-conormal-semilinear-difference-homotopy, with identity coefficient maps.
2. Set `D = R/I²` and `M = I/I²`; then `M² = 0`. Lift the variables `E` into `D`.
Apply lem-weil-pbc-localization-square-zero-lifting to extend this polynomial map across
`W`, obtaining `ell : P → D` over `B`. It kills `J²` and carries `J` into `M`.
3. The derivation `r ↦ 1 ⊗ dr` kills `I²` by Leibniz, giving `dbar`. The analogous
construction works for `P/J²`. Both restrict to the conormal differential, by representatives.
4. Restrict `ell` to obtain `gMinus`; its `B`-linearity follows because the action on
`M` factors through `B`. The universal property in def-weil-pbc-kahler-differentials
applied to `dbar ∘ ell` gives `gZero`. On `[h]` both composites in the chain equation
are `dbar(ell(h))`, proving that equation and both formulas.
5. Lift `ell a` to a polynomial map `t : R → R`. Its induced two-term map is `g N(a)`.
Apply lem-trf-conormal-semilinear-difference-homotopy to `t` and the identity to obtain
`HR`, with `gMinus N(a)Minus - id = HR δR` and `gZero N(a)Zero - id = δR HR`.
6. Let `aBar : R/I² → P/J²` be induced by `a`. The difference `aBar ell - qP` takes
values in `J/J²` and is an `A`-derivation since that ideal is square-zero. The universal
property of differentials gives `HP(b ⊗ dp) = b (aBar ell(p) - qP(p))`.
7. Evaluate on `[h]` to obtain the degree minus-one homotopy equation for `P`. On
`b ⊗ dp` use `dbarP aBar = N(a)Zero dbar`, verified on every quotient representative,
to obtain the degree-zero equation. These generators span. This proves both homotopies,
including for empty or infinite variable sets and `W = {1}`. -/
theorem localizedPresentation_homotopy_equivalence
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (R : Extension.{w} A B) (P : Extension.{w'} A B)
    (V : Type i) (E : Type j) (eR : R.Ring ≃ₐ[A] MvPolynomial V A)
    [Algebra (MvPolynomial E A) P.Ring] [IsScalarTower A (MvPolynomial E A) P.Ring]
    (W : Submonoid (MvPolynomial E A)) [IsLocalization W P.Ring] :
    Nonempty (R.Hom P) ∧
    ∀ a : R.Hom P,
      ∃ (ell : P.Hom R.infinitesimal)
        (dbar : R.infinitesimal.Ring →ₗ[A] R.CotangentSpace)
        (gMinus : P.Cotangent →ₗ[B] R.Cotangent)
        (gZero : P.CotangentSpace →ₗ[B] R.CotangentSpace)
        (HR : R.CotangentSpace →ₗ[B] R.Cotangent)
        (HP : P.CotangentSpace →ₗ[B] P.Cotangent),
        (∀ r : R.Ring, dbar (R.toInfinitesimal r) =
          (1 : B) ⊗ₜ[R.Ring] KaehlerDifferential.D A R.Ring r) ∧
        (∀ h : P.ker, R.ker.cotangentToQuotientSquare (gMinus (Cotangent.mk h)).val =
          ell h) ∧
        (∀ (p : P.Ring) (b : B),
          gZero (b ⊗ₜ[P.Ring] KaehlerDifferential.D A P.Ring p) = b • dbar (ell p)) ∧
        R.cotangentComplex ∘ₗ gMinus = gZero ∘ₗ P.cotangentComplex ∧
        gMinus ∘ₗ Cotangent.map a - LinearMap.id = HR ∘ₗ R.cotangentComplex ∧
        gZero ∘ₗ CotangentSpace.map a - LinearMap.id = R.cotangentComplex ∘ₗ HR ∧
        Cotangent.map a ∘ₗ gMinus - LinearMap.id = HP ∘ₗ P.cotangentComplex ∧
        CotangentSpace.map a ∘ₗ gZero - LinearMap.id = P.cotangentComplex ∘ₗ HP := by
  sorry

end Algebra.Extension
