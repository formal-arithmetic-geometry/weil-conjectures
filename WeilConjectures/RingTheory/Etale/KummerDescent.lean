/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Invariant.Kummer
public import WeilConjectures.RingTheory.Etale.InvariantsDescent

/-!
# Descent of étaleness along a tame Kummer cover

Let `R` be a Noetherian local ring, `π` in its maximal ideal, `n ≠ 0` invertible in `R` and
`ζ ∈ R` with `ζⁿ = 1` such that `1 - ζⁱ` is a unit for `0 < i < n` (e.g. the image of a
primitive `n`-th root of unity of a domain, `IsPrimitiveRoot.isUnit_one_sub_pow`). Let
`R' = R[t] ⧸ (tⁿ - π)` with the Kummer action of `ZMod n` by `t ↦ ζ t`. A finite étale
`R'`-algebra `T'` with a semilinear `ZMod n`-action whose closed fibre is split with trivial
action descends: its invariants `T` are finite étale over `R`
(`RingTheory.InvariantsDescent.etale_and_finite_of_kummer`). This is the trait case of the
spreading theorem for finite étale Galois covers (blueprint
`sbc-thm-spreading-finite-etale-galois`, [Stacks 0EYJ]).
-/

@[expose] public section

open Polynomial IsLocalRing

namespace RingTheory.InvariantsDescent

/-- **Descent of étaleness along a tame Kummer cover** `R → R' = R[t] ⧸ (tⁿ - π)`: the
specialisation of `etale_and_finite_of_isInvariant` to the Kummer action of `ZMod n`. -/
theorem etale_and_finite_of_kummer {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (n : ℕ) [NeZero n] (π : R) [Fact (π ∈ maximalIdeal R)] {ζ : R}
    (hζ : ζ ^ n = 1) (hu : ∀ i, 0 < i → i < n → IsUnit (1 - ζ ^ i)) (hn : IsUnit (n : R))
    {T : Type*} [CommRing T] [Algebra R T] {T' : Type*} [CommRing T']
    [Algebra (AdjoinRoot (X ^ n - C π)) T'] [Algebra R T']
    [IsScalarTower R (AdjoinRoot (X ^ n - C π)) T'] [Algebra T T'] [IsScalarTower R T T']
    [MulSemiringAction (Multiplicative (ZMod n)) T']
    (hdist : letI := AdjoinRoot.kummerAction n π hζ
      SMulDistribClass (Multiplicative (ZMod n)) (AdjoinRoot (X ^ n - C π)) T')
    [SMulCommClass (Multiplicative (ZMod n)) T T']
    [Algebra.IsInvariant T T' (Multiplicative (ZMod n))]
    [Algebra.Etale (AdjoinRoot (X ^ n - C π)) T'] [Module.Finite (AdjoinRoot (X ^ n - C π)) T']
    (hT : Function.Injective (algebraMap T T'))
    {k : ℕ} (hk : Module.finrank (AdjoinRoot (X ^ n - C π)) T' ≤ k)
    (φ : Fin k → (T' →ₐ[AdjoinRoot (X ^ n - C π)] ResidueField (AdjoinRoot (X ^ n - C π))))
    (hφ : Function.Injective φ)
    (hφΓ : ∀ j (g : Multiplicative (ZMod n)) (t : T'), φ j (g • t) = φ j t) :
    Algebra.Etale R T ∧ Module.Finite R T := by
  let := AdjoinRoot.kummerAction n π hζ
  have := AdjoinRoot.smulCommClass_kummerAction n π hζ
  have := AdjoinRoot.isInvariant_kummerAction n π hζ hu
  have : Module.Finite R (AdjoinRoot (X ^ n - C π)) :=
    (AdjoinRoot.powerBasis' (monic_X_pow_sub_C π (NeZero.ne n))).finite
  exact etale_and_finite_of_isInvariant (Γ := Multiplicative (ZMod n))
    (AdjoinRoot.injective_algebraMap_X_pow_sub_C n π) hT (by simpa using hn)
    (fun g x ↦ AdjoinRoot.residue_kummerAction_smul n π hζ (AdjoinRoot.root_mem_maximalIdeal n π)
      g x) hk φ hφ hφΓ

end RingTheory.InvariantsDescent
