/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Sheaf.RingTheory.HenselizationAtPrime
import Sheaf.RingTheory.GeneralizedHenselizationAtPrime

/-!
# Artin theorem for an embedded join of henselizations

Source: Hübner--Schmidt, *A tame site for the Weil conjectures*, Theorem 6.1, printed p. 12,
quoting Artin, *On the joins of Hensel rings*, Theorems 2.2 and 2.5
(blueprint: lem-trf-artin-embedded-hensel-join).
-/

@[expose] public section

universe u v

open Set

/-- For a normal integral domain `P`, the subring generated in a fixed separable closure of
`Frac P` by embedded ordinary henselizations at two primes is henselian local.  For incomparable
primes it is strictly henselian, and the contraction of its maximal ideal to `P` is strictly
contained in each prime.  Source: Hübner--Schmidt, Theorem 6.1, printed p. 12, quoting Artin,
Theorems 2.2 and 2.5 (blueprint: lem-trf-artin-embedded-hensel-join).

The proof uses the two clauses of that theorem.  Artin's Theorem 2.2 gives henselian locality of
the join of the two embedded henselizations.  Under the incomparability hypothesis, Artin's
Theorem 2.5 gives strict henselianity and strict containment of the contraction of the maximal
ideal.  The notions of normal domain, separable closure, henselization at a prime, and strict
henselian local ring are supplied by the cited dependency declarations.
-/
theorem artin_embedded_hensel_join
    (P : Type u) [CommRing P] [IsDomain P] [IsIntegrallyClosed P]
    (Ksep : Type v) [Field Ksep]
    [Algebra (FractionRing P) Ksep] [IsSepClosure (FractionRing P) Ksep]
    (q₁ q₂ : Ideal P) [q₁.IsPrime] [q₂.IsPrime]
    (H₁ H₂ : Type u) [CommRing H₁] [CommRing H₂]
    [Algebra (Localization.AtPrime q₁) H₁]
    [Algebra (Localization.AtPrime q₂) H₂]
    [HenselianLocalRing H₁] [HenselianLocalRing H₂]
    (hH₁ : Algebra.IsHenselizationAtPrime P q₁ H₁)
    (hH₂ : Algebra.IsHenselizationAtPrime P q₂ H₂)
    (e₁ : H₁ →+* Ksep) (e₂ : H₂ →+* Ksep)
    (he₁ : Function.Injective e₁) (he₂ : Function.Injective e₂)
    (compat₁ : e₁.comp ((algebraMap (Localization.AtPrime q₁) H₁).comp
      (algebraMap P (Localization.AtPrime q₁))) =
      (algebraMap (FractionRing P) Ksep).comp (algebraMap P (FractionRing P)))
    (compat₂ : e₂.comp ((algebraMap (Localization.AtPrime q₂) H₂).comp
      (algebraMap P (Localization.AtPrime q₂))) =
      (algebraMap (FractionRing P) Ksep).comp (algebraMap P (FractionRing P))) :
    HenselianLocalRing (Subring.closure (Set.range e₁ ∪ Set.range e₂)) ∧
      ((¬q₁ ≤ q₂ ∧ ¬q₂ ≤ q₁) →
        ∃ hJ : HenselianLocalRing (Subring.closure (Set.range e₁ ∪ Set.range e₂)),
          (IsStrictlyHenselianLocalRing (Subring.closure (Set.range e₁ ∪ Set.range e₂)) ∧
            Ideal.comap
              (RingHom.codRestrict
                ((algebraMap (FractionRing P) Ksep).comp (algebraMap P (FractionRing P)))
                (Subring.closure (Set.range e₁ ∪ Set.range e₂))
                (fun p => by
                  rw [← congrArg (fun f : P →+* Ksep => f p) compat₁]
                  exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)))
              (@IsLocalRing.maximalIdeal (Subring.closure (Set.range e₁ ∪ Set.range e₂))
                _ (@HenselianLocalRing.toIsLocalRing _ _ hJ)) < q₁) ∧
            Ideal.comap
              (RingHom.codRestrict
                ((algebraMap (FractionRing P) Ksep).comp (algebraMap P (FractionRing P)))
                (Subring.closure (Set.range e₁ ∪ Set.range e₂))
                (fun p => by
                  rw [← congrArg (fun f : P →+* Ksep => f p) compat₁]
                  exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)))
              (@IsLocalRing.maximalIdeal (Subring.closure (Set.range e₁ ∪ Set.range e₂))
                _ (@HenselianLocalRing.toIsLocalRing _ _ hJ)) < q₂) := by
  sorry

end
