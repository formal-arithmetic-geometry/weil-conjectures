/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q57
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Localization.Integral
import Mathlib.GroupTheory.Perm.Cycle.Type
import Sheaf.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres
import Sheaf.FieldTheory.FiniteDVRInertiaOrderPrimePart

/-!
# Finite DVR normalization and its tame inertia character

Source: Stacks Project, More on Algebra, Tags 09E8 and 09EE,
`literature/stacks-project/more-algebra.tex`, Remark `remark-finite-separable-extension`
and Lemma `lemma-galois-inertia`, equation `equation-inertia-character`.
(blueprint: lem-exc-finite-dvr-tame-inertia)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped Pointwise

namespace IsDiscreteValuationRing

/-- Finite normalization of a DVR and the tame inertia character at every maximal ideal.
The maps `j` and `ρ` are characterized on the original rings: `j` extends the inclusion
of the integral closure in `L`, and `ρ` is the induced residue-field embedding.
The integer `e` is the normalized additive valuation of every base uniformizer.
The character formula is required for every local uniformizer, expressing independence
of that choice. Its kernel, mapped into the decomposition group, is normal there.
The final equivalence agrees with the character on every quotient representative.

Source: Stacks Project, More on Algebra, Tags 09E8 and 09EE, Remark
`remark-finite-separable-extension`, Lemma `lemma-galois-inertia`, and equation
`equation-inertia-character`; Fields, Tag 09HW for roots of unity.
(blueprint: lem-exc-finite-dvr-tame-inertia)

Proof:
1. A DVR is a PID (`def-sc-discrete-valuation-ring`), hence Noetherian and normal
   (`lem-weil-pbc-pid-noetherian-normal`), and has dimension one
   (`lem-sc-dvr-dimension-one`). Finite separability gives finite normalization
   (`lem-weil-pbc-noetherian-normal-separable-integral-closure-finite`).
2. The normalization is Dedekind with finite residue extensions by
   `lem-sc-integral-closure-dedekind-surjective-fibres`; its maximal localizations
   are DVRs by `lem-sc-dedekind-localization-dvr`. Its fraction field is L by
   `lem-weil-pbc-integral-closure-finite-extension-normal`, and localization does
   not change that field. Localizing and then taking the residue field gives
   precisely the prime's residue field (`def-weil-pbc-localization-at-prime`).
3. The contraction of the maximal ideal is maximal: a field integral over a
   subdomain forces that subdomain to be a field, since a monic equation for
   the inverse of a nonzero element expresses the inverse in the subdomain.
   Thus the contraction is the maximal ideal of A. The local map gives e > 0
   and π_A = u t^e. Automorphisms preserve integral elements and those fixing
   the ideal extend to fractions b/s by σ(b)/σ(s). The inertia group is the
   kernel of the residue action of its stabilizer and is normal there.
4. Apply `lem-exc-dvr-inertia-order-prime-part`: if n is the prime-to-p part of e,
   then |I| = n p^b. This allows inseparable residue extensions; |I| = e is
   not assumed.
5. Write σ(t) = a_σ t with a_σ a unit. Applying σ to π_A = u t^e gives
   u = σ(u) a_σ^e. Inertia acts trivially on residues, so the residue of a_σ
   is an e-th root. The identity a_(στ) = σ(a_τ) a_σ proves multiplicativity.
   For t' = z t the ratio changes by σ(z)/z, whose residue is one, so the
   same character satisfies the formula for every uniformizer.
6. If δ is in the stabilizer and σ is in the kernel, use the uniformizer
   t' = δ⁻¹(t). The residue of (δσδ⁻¹)(t)/t is the residue action of δ
   applied to the character of σ computed with t', and hence is one.
   This proves normality of the kernel in the decomposition group.
7. For σ in the kernel, (σ - 1)(t^i C) is contained in t^(i+1) C, by reducing
   σ(t)/t and σ(a) for t^i a. For σ ≠ 1 of order m choose c not fixed by σ
   (otherwise σ fixes Frac(C) = L). Write d = σ(c) - c = t^i a with a a unit
   and finite i ≥ 1. Then σ^j(d) ≡ d modulo t^(i+1) for every j. Telescoping
   σ^m(c) - c gives m d ≡ 0 modulo t^(i+1). Divide by t^i and reduce:
   m times the nonzero residue of a is zero, so p divides m.
8. The kernel is finite. Cauchy's theorem (`lem-exc-finite-group-cauchy`)
   supplies an element of order q for every prime divisor q of its order.
   Step 7 forces q = p. Prime factorization gives order p^a, including a = 0.
9. Write e = n p^s. In characteristic p the binomial coefficients between
   the endpoints vanish, so (X^n - 1)^(p^s) = X^e - 1. In a field a power
   vanishes only when its base does; therefore μ_e = μ_n. By
   `lem-exc-field-roots-cyclic-bound`, μ_n is finite cyclic of order at most n.
   The order of a generator divides n, hence the image order divides n and
   is prime to p.
10. Every character fibre is a coset of its kernel. Thus |I| = |P| |im χ|.
    Compare with Steps 4 and 8 and take prime-to-p parts to obtain |im χ| = n.
    The image lies in μ_n, whose order is at most n, so it is all of μ_n and
    that group has order n. The map σP ↦ χ(σ) is well-defined and surjective;
    equality of values says the quotient of the representatives lies in P,
    proving injectivity and giving the asserted induced isomorphism. -/
theorem finite_normalization_tame_inertia
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p] :
    Module.Finite A (integralClosure A L) ∧
      ∀ (𝔫 : Ideal (integralClosure A L)) [𝔫.IsMaximal],
        ∃ hC : IsDiscreteValuationRing (Localization.AtPrime 𝔫),
          ∃ j : Localization.AtPrime 𝔫 →+* L,
            (∀ b : integralClosure A L,
              j (algebraMap (integralClosure A L) (Localization.AtPrime 𝔫) b) = (b : L)) ∧
            @IsFractionRing (Localization.AtPrime 𝔫) _ L _ j.toAlgebra ∧
            ∃ ρ : IsLocalRing.ResidueField A →+* 𝔫.ResidueField,
              (∀ a : A, ρ (IsLocalRing.residue A a) = algebraMap A 𝔫.ResidueField a) ∧
              @Module.Finite (IsLocalRing.ResidueField A) 𝔫.ResidueField _ _
                ρ.toAlgebra.toModule ∧
              ∃ e : ℕ,
                (∀ π : A, Irreducible π →
                  @addVal (Localization.AtPrime 𝔫) _ _ hC
                    (algebraMap A (Localization.AtPrime 𝔫) π) = (e : ℕ∞)) ∧
                ∃ χ : 𝔫.inertia (MulAction.stabilizer Gal(L/K) 𝔫) →*
                    rootsOfUnity e 𝔫.ResidueField,
                  (∀ (t : Localization.AtPrime 𝔫), Irreducible t →
                    ∀ σ : 𝔫.inertia (MulAction.stabilizer Gal(L/K) 𝔫),
                      ∃ a : (Localization.AtPrime 𝔫)ˣ,
                        j (a : Localization.AtPrime 𝔫) = σ.1.1 (j t) / j t ∧
                        ((χ σ : 𝔫.ResidueFieldˣ) : 𝔫.ResidueField) =
                          IsLocalRing.residue (Localization.AtPrime 𝔫) a) ∧
                  (χ.ker.map (𝔫.inertia (MulAction.stabilizer Gal(L/K) 𝔫)).subtype).Normal ∧
                  Finite χ.ker ∧ (∃ a : ℕ, Nat.card χ.ker = p ^ a) ∧
                  rootsOfUnity e 𝔫.ResidueField =
                    rootsOfUnity (e / p ^ e.factorization p) 𝔫.ResidueField ∧
                  IsCyclic (rootsOfUnity (e / p ^ e.factorization p) 𝔫.ResidueField) ∧
                  Nat.card (rootsOfUnity (e / p ^ e.factorization p) 𝔫.ResidueField) =
                    e / p ^ e.factorization p ∧
                  ∃ θ : (𝔫.inertia (MulAction.stabilizer Gal(L/K) 𝔫) ⧸ χ.ker) ≃*
                      rootsOfUnity (e / p ^ e.factorization p) 𝔫.ResidueField,
                    ∀ σ : 𝔫.inertia (MulAction.stabilizer Gal(L/K) 𝔫),
                      (θ (QuotientGroup.mk σ) : 𝔫.ResidueFieldˣ) = (χ σ : 𝔫.ResidueFieldˣ) := by
  sorry

end IsDiscreteValuationRing
