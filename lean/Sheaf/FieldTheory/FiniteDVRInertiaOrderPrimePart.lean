/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q111
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.Notation
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Sheaf.FieldTheory.FiniteDVRResidueNormalAction
import Sheaf.NumberTheory.DvrGaloisDegreeData

/-!
# Prime-to-residue-characteristic part of finite inertia order

Source: Stacks Project, `literature/stacks-project/more-algebra.tex`,
Tag 09EE (lemma-galois-inertia), first proof paragraph
(blueprint: lem-exc-dvr-inertia-order-prime-part).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped Pointwise

namespace IsDiscreteValuationRing

/-- For a finite normal separable extension of fraction fields of a DVR, the inertia
subgroup at a maximal ideal has order whose prime-to-residue-characteristic part is the
prime-to-residue-characteristic part of the ramification index. The residue extension is
allowed to be inseparable.

Source: Stacks Project, `literature/stacks-project/more-algebra.tex`, Tag 09EE
(lemma-galois-inertia), first proof paragraph (blueprint: lem-exc-dvr-inertia-order-prime-part).

Proof (following the five steps in the node). (1) Write `G = Aut_K(L)`. By
`lem-weil-pbc-finite-galois-fixed-field`, `G` is finite and `Nat.card G = [L : K]`.
By `lem-exc-dvr-galois-degree-data`, the finite set of maximal ideals of the
integral closure has cardinality `g > 0`, the residue degree at `𝔫` is `f > 0`,
the common ramification index is the exponent `e` in `hπ`, and
`Nat.card G = g * e * f`; `G` acts transitively on those ideals. (2) The map
from `G` to that set sending `σ` to `σ(𝔫)` is onto. Its fibres are left cosets
of `D = MulAction.stabilizer G 𝔫`, so orbit-stabilizer gives
`Nat.card D = e * f`. (3) Put `E = B / 𝔫`. By
`lem-exc-dvr-residue-normal-action`, `E` is normal over the residue field and
the residue-action map `D → Aut(E/k)` is onto; its kernel is exactly the inertia
subgroup in the conclusion. (4) The residue extension has characteristic `p`
and degree `f`. By `lem-exc-normal-field-degree-factors`, the order `h` of its
automorphism group satisfies `f = h * p^c` for some `c ≥ 0`. (5) Counting the
fibres of the residue-action map gives `Nat.card I = e * p^c`. Factoring the
positive integer `e` as `p^a * m` with `p ∤ m`, the maximal divisor of `e`
coprime to `p` is `m`; hence the supplied `n` equals `m` and
`Nat.card I = n * p^(a+c)`. This proves the stated existential, while the
finite-group input in (1) proves `Finite I`.
-/
theorem inertia_order_prime_part
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
    (𝔫 : Ideal (integralClosure A L)) [𝔫.IsMaximal]
    [hC : IsDiscreteValuationRing (Localization.AtPrime 𝔫)]
    [hlocal : IsLocalHom (algebraMap A (Localization.AtPrime 𝔫))]
    (πA : A) (hπA : IsLocalRing.maximalIdeal A = Ideal.span {πA})
    (t : Localization.AtPrime 𝔫)
      (ht : IsLocalRing.maximalIdeal (Localization.AtPrime 𝔫) = Ideal.span {t})
    (e : ℕ) (he : 0 < e)
    (u : (Localization.AtPrime 𝔫)ˣ)
    (hπ : algebraMap A (Localization.AtPrime 𝔫) πA = (u : Localization.AtPrime 𝔫) * t ^ e)
    (n : ℕ) (hn_dvd : n ∣ e) (hn_coprime : Nat.Coprime n p)
    (hn_max : ∀ d : ℕ, d ∣ e → Nat.Coprime d p → d ≤ n) :
    Finite (𝔫.inertia (MulAction.stabilizer Gal(L / K) 𝔫)) ∧
      ∃ b : ℕ, Nat.card (𝔫.inertia (MulAction.stabilizer Gal(L / K) 𝔫)) = n * p ^ b := by
  sorry

end IsDiscreteValuationRing
