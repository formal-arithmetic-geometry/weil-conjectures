/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.FieldTheory.FiniteDVRTameInertia
public import Mathlib.FieldTheory.Galois.Notation
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.RingTheory.Localization.Integral

/-!
# Wild inertia surjectivity and scaled tame characters in finite towers

Source: Stacks Project, More on Algebra, Tags 0BU7 and 0BU8,
`literature/stacks-project/more-algebra.tex`, Lemma `lemma-compare-inertia` and
Remark `remark-canonical-inertia-character`.
(blueprint: lem-exc-finite-tame-character-tower)
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

open scoped Pointwise

namespace IsDiscreteValuationRing

/-- Restriction in a finite Galois tower is surjective on decomposition, inertia and wild
inertia groups. The canonical tame characters have the wild kernels and commute with the
power map whose exponent is the ratio of the prime-to-residue-characteristic indices.

The first clause establishes maximality of the contracted ideal. The remaining clauses
use any maximal ideal equal to that contraction. The local embeddings `jL`, `jM` extend the
inclusions of the integral closures. As in `finite_normalization_tame_inertia`, the raw
characters are characterized by the residue of `σ(t)/t` for every local uniformizer, and
the indices are the normalized additive valuations of every base uniformizer. Thus the
existential characters and embeddings are fixed by their defining formulas.

Source: Stacks Project, More on Algebra, Tags 0BU7 and 0BU8.
(blueprint: lem-exc-finite-tame-character-tower)

Proof:
1. The integral closure in M is integral over the integral closure in L
   (`def-weil-pbc-integral-closure`). A monic equation for the inverse of a nonzero
   element shows that a field integral over a subdomain forces that subdomain to be a field.
   Apply this to the quotient by the contracted maximal ideal; it is maximal.
2. Apply `lem-exc-finite-dvr-tame-inertia` to L/K and M/K. This supplies the local DVRs,
   the embeddings extending the inclusions, normalized indices, uniformizer characters,
   finite p-group wild kernels, and cyclic tame quotients of order the prime-to-p indices.
3. By `lem-weil-pbc-integral-closure-algebraic-extension-normal`, both normalizations are
   normal domains with fraction fields L and M. Integrality over the lower normalization
   is equivalent to membership in the upper one. Also M/L is finite Galois.
4. Lift an element of the lower decomposition group by
   `lem-weil-pbc-normal-subextension-automorphism-extends`. The image of the upper prime
   and the chosen upper prime lie over the same lower prime. Apply prime conjugacy in
   `lem-exc-finite-galois-prime-residue-lifting` over the lower normalization and correct
   the lift by an automorphism over L. This proves decomposition surjectivity.
5. For a lower inertia element, the residue action of such a lift fixes the lower residue
   field. The residue-lifting clause of the same prime-residue lemma supplies an
   automorphism over L with that residue action. Correct the lift by its inverse to
   obtain upper inertia. Contraction and residue-field injection show that restriction
   maps the decomposition and inertia groups into the lower groups.
6. The local inclusion sends a lower uniformizer to u times the r-th power of an upper
   uniformizer, with u a unit and r positive. Apply the normalized valuations of
   `def-sc-discrete-valuation-ring` to get eM = r eL, hence nL divides nM.
7. Applying upper inertia to that uniformizer equation and reducing cancels σ(u)/u.
   The uniformizer formula of `lem-exc-finite-dvr-tame-inertia` therefore gives the raw
   character relation χL(σ|L) = χM(σ)^r. In particular wild inertia maps into wild inertia.
8. Lift a lower wild element γ to upper inertia τ. Since χM(τ)^nM = 1, τ^nM is wild.
   The order of γ divides a p-power by `lem-exc-finite-dvr-tame-inertia`; choose h with
   h nM congruent to 1 modulo that p-power. Then τ^(h nM) is a wild lift of γ.
9. Raise the raw identity to qL and use r qL = qM (nM/nL). This is the asserted scaled
   character identity under the canonical residue-field embedding.
10. Raising to qX is an automorphism of the nX-th roots of unity, since qX is a p-power
    and nX is prime to p (use a Bezout inverse). The surjectivity and kernels from
    `lem-exc-finite-dvr-tame-inertia` are preserved. Thus the identity describes the
    induced transition on the tame quotients, and that transition is surjective. -/
theorem finite_tame_character_tower
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (M : Type z) [Field M] [Algebra K M] [Algebra A M] [Algebra L M]
    [IsScalarTower A K M] [IsScalarTower A L M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
    (𝔫M : Ideal (integralClosure A M)) [𝔫M.IsMaximal] :
    (Ideal.comap (IsScalarTower.toAlgHom A L M).mapIntegralClosure.toRingHom 𝔫M).IsMaximal ∧
    ∀ (𝔫L : Ideal (integralClosure A L)) [𝔫L.IsMaximal]
      (hcomp : 𝔫L = Ideal.comap
        (IsScalarTower.toAlgHom A L M).mapIntegralClosure.toRingHom 𝔫M),
    ∃ (hCL : IsDiscreteValuationRing (Localization.AtPrime 𝔫L))
      (hCM : IsDiscreteValuationRing (Localization.AtPrime 𝔫M))
      (jL : Localization.AtPrime 𝔫L →+* L) (jM : Localization.AtPrime 𝔫M →+* M),
      (∀ b : integralClosure A L,
        jL (algebraMap (integralClosure A L) (Localization.AtPrime 𝔫L) b) = (b : L)) ∧
      (∀ b : integralClosure A M,
        jM (algebraMap (integralClosure A M) (Localization.AtPrime 𝔫M) b) = (b : M)) ∧
    ∃ (eL eM : ℕ),
      (∀ πA : A, Irreducible πA →
        @addVal (Localization.AtPrime 𝔫L) _ _ hCL
          (algebraMap A (Localization.AtPrime 𝔫L) πA) = (eL : ℕ∞)) ∧
      (∀ πA : A, Irreducible πA →
        @addVal (Localization.AtPrime 𝔫M) _ _ hCM
          (algebraMap A (Localization.AtPrime 𝔫M) πA) = (eM : ℕ∞)) ∧
    ∃ (χL : 𝔫L.inertia (MulAction.stabilizer Gal(L/K) 𝔫L) →*
        rootsOfUnity eL 𝔫L.ResidueField)
      (χM : 𝔫M.inertia (MulAction.stabilizer Gal(M/K) 𝔫M) →*
        rootsOfUnity eM 𝔫M.ResidueField),
      (∀ t : Localization.AtPrime 𝔫L, Irreducible t →
        ∀ σ : 𝔫L.inertia (MulAction.stabilizer Gal(L/K) 𝔫L),
          ∃ a : (Localization.AtPrime 𝔫L)ˣ,
            jL (a : Localization.AtPrime 𝔫L) = σ.1.1 (jL t) / jL t ∧
            ((χL σ : 𝔫L.ResidueFieldˣ) : 𝔫L.ResidueField) =
              IsLocalRing.residue (Localization.AtPrime 𝔫L) a) ∧
      (∀ t : Localization.AtPrime 𝔫M, Irreducible t →
        ∀ σ : 𝔫M.inertia (MulAction.stabilizer Gal(M/K) 𝔫M),
          ∃ a : (Localization.AtPrime 𝔫M)ˣ,
            jM (a : Localization.AtPrime 𝔫M) = σ.1.1 (jM t) / jM t ∧
            ((χM σ : 𝔫M.ResidueFieldˣ) : 𝔫M.ResidueField) =
              IsLocalRing.residue (Localization.AtPrime 𝔫M) a) ∧
    ∃ (qL nL qM nM : ℕ),
      (∃ aL : ℕ, qL = p ^ aL) ∧ (∃ aM : ℕ, qM = p ^ aM) ∧
      Nat.Coprime nL p ∧ Nat.Coprime nM p ∧
      eL = qL * nL ∧ eM = qM * nM ∧ nL ∣ nM ∧
    ∃ (rD : MulAction.stabilizer Gal(M/K) 𝔫M →* MulAction.stabilizer Gal(L/K) 𝔫L),
      Function.Surjective rD ∧
      (∀ σ : MulAction.stabilizer Gal(M/K) 𝔫M,
        (rD σ).1 = AlgEquiv.restrictNormalHom L σ.1) ∧
    ∃ (rI : 𝔫M.inertia (MulAction.stabilizer Gal(M/K) 𝔫M) →*
        𝔫L.inertia (MulAction.stabilizer Gal(L/K) 𝔫L)),
      Function.Surjective rI ∧
      (∀ σ : 𝔫M.inertia (MulAction.stabilizer Gal(M/K) 𝔫M),
        (rI σ).1.1 = AlgEquiv.restrictNormalHom L σ.1.1) ∧
    ∃ (rP : χM.ker →* χL.ker),
      Function.Surjective rP ∧ (∀ σ : χM.ker, (rP σ).1 = rI σ.1) ∧
    ∃ (χLcan : 𝔫L.inertia (MulAction.stabilizer Gal(L/K) 𝔫L) →*
        rootsOfUnity nL 𝔫L.ResidueField)
      (χMcan : 𝔫M.inertia (MulAction.stabilizer Gal(M/K) 𝔫M) →*
        rootsOfUnity nM 𝔫M.ResidueField),
      (∀ σ : 𝔫L.inertia (MulAction.stabilizer Gal(L/K) 𝔫L),
        (χLcan σ : 𝔫L.ResidueFieldˣ) = (χL σ : 𝔫L.ResidueFieldˣ) ^ qL) ∧
      (∀ σ : 𝔫M.inertia (MulAction.stabilizer Gal(M/K) 𝔫M),
        (χMcan σ : 𝔫M.ResidueFieldˣ) = (χM σ : 𝔫M.ResidueFieldˣ) ^ qM) ∧
      Function.Surjective χLcan ∧ Function.Surjective χMcan ∧
      χLcan.ker = χL.ker ∧ χMcan.ker = χM.ker ∧
      ∀ σ : 𝔫M.inertia (MulAction.stabilizer Gal(M/K) 𝔫M),
        Units.map (Ideal.ResidueField.map 𝔫L 𝔫M
            (IsScalarTower.toAlgHom A L M).mapIntegralClosure.toRingHom hcomp).toMonoidHom
            (χLcan (rI σ) : 𝔫L.ResidueFieldˣ) =
          (χMcan σ : 𝔫M.ResidueFieldˣ) ^ (nM / nL) := by
  sorry

end IsDiscreteValuationRing
