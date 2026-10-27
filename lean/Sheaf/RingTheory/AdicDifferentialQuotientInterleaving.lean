/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q129
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.FieldTheory.Separable
public import Sheaf.RingTheory.ContinuousKaehlerDifferential
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Unramified.Field

/-! # Interleaving maps for adic quotient differentials

Source: Stacks Project, Algebra, Tags 00RO, 07BK, 05GG and 090W; the adjacent-quotient
comparison expanded in the DAG node (blueprint: lem-trf-adic-differential-quotient-interleaving).

The fixed compatible `F`-algebra structure on the completion represents the map `σ`.
The index `n` represents the positive exponent `r = n + 1`. The completed-module
quotient uses `J^r N = I^r N`, making its completed-ring scalar action explicit.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

namespace AdicDifferentialInterleaving

/-- The extended ideal `J = IC` in `C = AdicCompletion I A`.
Source: Stacks Project, Algebra, Tag 05GG
(blueprint: lem-trf-adic-differential-quotient-interleaving). -/
abbrev completionIdeal {A : Type v} [CommRing A] (I : Ideal A) :
    Ideal (AdicCompletion I A) :=
  I.map (algebraMap A (AdicCompletion I A))

variable (k : Type u) (A : Type v) [CommRing k] [CommRing A] [Algebra k A]

/-- The positive-level completed differential quotient `Q_(n+1) = N/J^(n+1)N`.
Here `N` is the completion of `Ω[A/k]`; its scalar action is Mathlib's componentwise
completion action. Since `J = IC`, the denominator equals `I^(n+1)N`.
Source: Stacks Project, Algebra, Tag 05GG
(blueprint: lem-trf-adic-differential-quotient-interleaving). -/
abbrev quotientModule (I : Ideal A) (n : ℕ) :=
  AdicCompletion I (KaehlerDifferential k A) ⧸
    (completionIdeal I ^ (n + 1) •
      (⊤ : Submodule (AdicCompletion I A) (AdicCompletion I (KaehlerDifferential k A))))

/-- Reduction `q_(n+1)` between adjacent completed differential quotients.
Source: Stacks Project, Algebra, Tag 05GG, canonical quotient reductions
(blueprint: lem-trf-adic-differential-quotient-interleaving). -/
abbrev moduleReduction (I : Ideal A) (n : ℕ) :
    quotientModule k A I (n + 1) →ₗ[AdicCompletion I A] quotientModule k A I n :=
  Submodule.factorPowSucc (completionIdeal I) (AdicCompletion I (KaehlerDifferential k A))
    (n + 1)

/-- The quotient differential symbol `da` in `Q_(n+1)`, using the canonical completion map.
Source: Stacks Project, Algebra, Tags 00RO and 05GG
(blueprint: lem-trf-adic-differential-quotient-interleaving). -/
abbrev moduleSymbol (I : Ideal A) (n : ℕ) (a : A) : quotientModule k A I n :=
  Submodule.Quotient.mk (AdicCompletion.of I (KaehlerDifferential k A)
    (KaehlerDifferential.D k A a))

variable (F : Type w) [CommRing F]

/-- The relative differential module `E_(n+1) = Ω[(C/J^(n+1))/F]`.
The given `F`-algebra structure on `C` is precisely the fixed coefficient map `σ`.
Source: Stacks Project, Algebra, Tags 07BK and 00RO
(blueprint: lem-trf-adic-differential-quotient-interleaving). -/
abbrev quotientDifferentials (I : Ideal A) [Algebra F (AdicCompletion I A)] (n : ℕ) :=
  KaehlerDifferential F (AdicCompletion I A ⧸ completionIdeal I ^ (n + 1))

/-- The differential symbol of `x mod J^(n+1)` in `E_(n+1)`.
Source: Stacks Project, Algebra, Tag 00RO
(blueprint: lem-trf-adic-differential-quotient-interleaving). -/
abbrev differentialSymbol (I : Ideal A) [Algebra F (AdicCompletion I A)] (n : ℕ)
    (x : AdicCompletion I A) : quotientDifferentials A F I n :=
  KaehlerDifferential.D F (AdicCompletion I A ⧸ completionIdeal I ^ (n + 1))
    (Ideal.Quotient.mk _ x)

/-- The induced transition `t_(n+1)` on quotient differentials, reusing the existing
positive-level differential transition without constructing another differential map.
Source: Stacks Project, Algebra, Tag 00RO, functoriality of differentials
(blueprint: lem-trf-adic-differential-quotient-interleaving). -/
abbrev differentialReduction (I : Ideal A) [Algebra F (AdicCompletion I A)] (n : ℕ) :
    quotientDifferentials A F I (n + 1) →ₗ[AdicCompletion I A]
      quotientDifferentials A F I n :=
  KaehlerDifferential.adicTransition F (AdicCompletion I A) (completionIdeal I) n

/-- Adic quotient differentials interleave with completed differentials. An additive
quotient map `δ` is an `F`-derivation: its vanishing on `F` and its Leibniz rule are stated
explicitly, with the latter checked on lifts from `C` to avoid an auxiliary scalar instance.

Source: Stacks Project, Algebra, Tags 00RO and 07BK; canonical quotient identifications
from Tag 05GG and coefficient annihilation from Tag 090W
(blueprint: lem-trf-adic-differential-quotient-interleaving).

Proof plan:
1. Apply lem-weil-pbc-module-completion-complete (Tag 05GG) to `A` and `Ω[A/k]`.
   The component projections are surjective with kernels the ideal-power multiples.
   They give the canonical identifications with `A/I^r` and `Ω[A/k]/I^rΩ[A/k]`.
   Componentwise multiplication shows `J^r N = I^r N` and gives all quotient actions.
2. The composite `Dσ` is a `k`-derivation on `F`. Universality of differentials and
   lem-trf-separable-field-differentials-vanish (Tag 090W) imply it is zero.
3. The derivation `a ↦ d(ι(a) mod J^r)` factors uniquely through `Ω[A/k]`, then
   through `Q_r` because `I^r` annihilates `E_r`. Surjectivity of `A → C/J^r`
   makes the resulting `α_r` `C`-linear. Differential symbols give uniqueness.
4. The assumed filtration bound makes reduction of `D` descend to `C/J^(r+1)`.
   Its Leibniz rule descends, and Step 2 makes it an `F`-derivation. Tag 00RO gives
   `β_r`, uniquely determined by the symbols `d(x mod J^(r+1))`.
5. Check the two transition identities on symbols; every map is `C`-linear.
6. On `da mod I^(r+1)`, use `D(ι(a)) = j(da)` and the canonical projection
   identification to obtain `β_r α_(r+1) = q_r`.
7. For a symbol from any `x : C`, lift `x mod J^(r+1)` to some `a : A` using
   Step 1. The filtration bound identifies its image under `β_r` with `da mod I^r`.
   Applying `α_r` gives `d(x mod J^r)`. Generation proves `α_r β_r = t_r`.
-/
theorem quotient_interleaving
    {k : Type u} {F : Type w} {A : Type v} [Field k] [Field F] [CommRing A]
    [Algebra k F] [Module.Finite k F] [Algebra.IsSeparable k F] [Algebra k A]
    (I : Ideal A) (hI : I.FG)
    [Algebra F (AdicCompletion I A)] [IsScalarTower k F (AdicCompletion I A)]
    (D : Derivation k (AdicCompletion I A) (AdicCompletion I (KaehlerDifferential k A)))
    (hD : ∀ a : A, D (algebraMap A (AdicCompletion I A) a) =
      AdicCompletion.of I (KaehlerDifferential k A) (KaehlerDifferential.D k A a))
    (hbound : ∀ (n : ℕ) (x : AdicCompletion I A),
      x ∈ completionIdeal I ^ (n + 2) → D x ∈
        completionIdeal I ^ (n + 1) •
          (⊤ : Submodule (AdicCompletion I A) (AdicCompletion I (KaehlerDifferential k A)))) :
    (∀ f : F, D (algebraMap F (AdicCompletion I A) f) = 0) ∧
    (∀ n : ℕ, ∃ δ :
      (AdicCompletion I A ⧸ completionIdeal I ^ (n + 2)) →+ quotientModule k A I n,
      (∀ x : AdicCompletion I A, δ (Ideal.Quotient.mk _ x) = Submodule.Quotient.mk (D x)) ∧
      (∀ f : F, δ (algebraMap F _ f) = 0) ∧
      (∀ x y : AdicCompletion I A,
        δ (Ideal.Quotient.mk _ (x * y)) =
          x • δ (Ideal.Quotient.mk _ y) + y • δ (Ideal.Quotient.mk _ x))) ∧
    ∃ (α : ∀ n : ℕ, quotientModule k A I n →ₗ[AdicCompletion I A]
        quotientDifferentials A F I n)
      (β : ∀ n : ℕ, quotientDifferentials A F I (n + 1) →ₗ[AdicCompletion I A]
        quotientModule k A I n),
      (∀ (n : ℕ) (a : A), α n (moduleSymbol k A I n a) =
        differentialSymbol A F I n (algebraMap A (AdicCompletion I A) a)) ∧
      (∀ (n : ℕ) (x : AdicCompletion I A), β n (differentialSymbol A F I (n + 1) x) =
        Submodule.Quotient.mk (D x)) ∧
      (∀ (n : ℕ) (α' : quotientModule k A I n →ₗ[AdicCompletion I A]
          quotientDifferentials A F I n),
        (∀ a : A, α' (moduleSymbol k A I n a) =
          differentialSymbol A F I n (algebraMap A (AdicCompletion I A) a)) → α' = α n) ∧
      (∀ (n : ℕ) (β' : quotientDifferentials A F I (n + 1) →ₗ[AdicCompletion I A]
          quotientModule k A I n),
        (∀ x : AdicCompletion I A, β' (differentialSymbol A F I (n + 1) x) =
          Submodule.Quotient.mk (D x)) → β' = β n) ∧
      (∀ n : ℕ, (differentialReduction A F I n).comp (α (n + 1)) =
        (α n).comp (moduleReduction k A I n)) ∧
      (∀ n : ℕ, (moduleReduction k A I n).comp (β (n + 1)) =
        (β n).comp (differentialReduction A F I (n + 1))) ∧
      (∀ n : ℕ, (β n).comp (α (n + 1)) = moduleReduction k A I n) ∧
      (∀ n : ℕ, (α n).comp (β n) = differentialReduction A F I n) := by
  sorry

end AdicDifferentialInterleaving
