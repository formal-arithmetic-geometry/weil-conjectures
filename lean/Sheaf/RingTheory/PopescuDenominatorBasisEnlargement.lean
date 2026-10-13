/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.RingTheory.PopescuAdmissibleSubalgebra
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.LinearAlgebra.Basis.Defs
import Sheaf.RingTheory.ArtinianLocalEssentiallyFiniteTypeResidue
import Sheaf.RingTheory.FlatAndFlatOfFlatFibreNoetherian
import Sheaf.RingTheory.HenselianEtaleRetraction
import Sheaf.RingTheory.HenselianFiniteEtaleEquivalence
import Sheaf.RingTheory.JacobiZariskiHomologySequence
import Sheaf.RingTheory.KaehlerDifferentialsPolynomialExtension
import Sheaf.RingTheory.LocalDimensionZeroHenselian
import WeilConjectures.Mathlib.RingTheory.Etale.Field

/-!
# Differential basis enlargement after clearing denominators

Source: Stacks Project, proofs of Tags 07FH and 07FI; the denominator and differential
argument in steps 5–14 of lem-weil-pbc-popescu-quotient-basis-enlargement.
-/

@[expose] public section

set_option autoImplicit false
universe u v

namespace Algebra

/-- Given a residue differential basis whose lifts have a common denominator, enlarge the
admissible subalgebra so that it captures a positive power of that denominator and has a
residue differential basis lifted from the original ring. No ideal generators are chosen.
Source: Stacks Project, proofs of Tags 07FH and 07FI, and steps 5–14 of
lem-weil-pbc-popescu-quotient-basis-enlargement.
(blueprint: lem-weil-pbc-popescu-denominator-basis-enlargement).

Proof: Write L = Λ_q, J = qL, B = L/J^n, F₀ = A₀/m₀, K = B/m_B, x = π(s), and
α = residue_B(x). Since n ≥ 1, B is Artinian local with maximal ideal JB, and s ∉ q
makes x a unit, hence α ≠ 0. Admissibility gives m₀B = m_B; contraction and maximality
then identify m₀ with A₀ ∩ m_B. This embeds F₀ into K and makes the inclusion local.
Put c_j = residue_A₀(a₀ j), so the hypotheses say dc_j form a basis over F₀.

If α is transcendental over F₀, localize A₀[T] at the preimage of m_B under evaluation
T ↦ x. Modulo m₀ this prime is zero in F₀[T], so the resulting ring D has residue
field F₀(T), maximal ideal m₀D, and is Artinian local. Evaluation extends to a local
map D → B. The Noetherian fibre flatness criterion applies to A₀ → D → B: B is flat
over A₀ and the fibre D/m₀D is a field, hence its module B/m₀B is flat. Thus D → B
is flat, faithfully flat, and injective. Its image A contains A₀ and x, is Artinian
local and flat into B, and m_A B = m_B. Its residue field F₀(α) is finitely generated
over k; the Artinian local essentially-finite-type residue criterion makes A
essentially of finite type over k. Polynomial and localization formulas for Kähler
differentials give the basis dc_j together with dα over F₀(α).

If α is algebraic over F₀, choose Q = p^e so β = α^Q is separable over F₀. The finite
separable field F₀(β) lifts, by the henselian finite étale equivalence for A₀, to a
finite étale Artinian local A₀-algebra D with maximal ideal m₀D. Base change to B,
use the residue embedding F₀(β) → K to select the prime with residue K, and apply
the henselian étale retraction for B. This yields a local map D → B extending A₀
and inducing that residue embedding. The same fibre criterion makes it flat and
injective. Its image A is admissible by the same residue finite-type criterion.
Finite separable base change for differentials gives the basis dc_j over F₀(β).

To capture a power in this case, lift β⁻¹ to a unit y of A. Then y x^Q = 1 + ε with
ε ∈ m_B. Choose a p-power q' ≥ max(n,p). Frobenius and m_B^n = 0 give
(y x^Q)^q' = 1, so x^(Qq') = y^(-q') ∈ A. Put N = Qq'. In the transcendental
case put N = p. In both cases N ≥ 1 and γ = x^N belongs to A and is a unit of B.
Its differential in the residue field of A vanishes: γ = α^p in the transcendental
case, and γ = β^q' in the separable case, with p dividing the relevant exponent.

Set xs_j = μ_j s^(N-1). The denominator equations give π(xs_j) = a₀_j γ ∈ A.
Their residue differentials are γ dc_j, so scaling by the nonzero scalar γ preserves
the basis. In the transcendental case append s, whose differential is dα; scale
only the original basis vectors. These xs and their explicitly specified images in
A give the required differential basis and the element c = x^N. The empty initial
basis is allowed: in the separable case it remains empty, and in the transcendental
case the only added vector is dα. -/
theorem exists_popescu_denominator_basis_enlargement
    (k : Type u) (Λ : Type v) [Field k] [CommRing Λ] [Algebra k Λ]
    [IsNoetherianRing Λ] (p : ℕ) [CharP k p] (hp : 0 < p)
    (q : Ideal Λ) [q.IsPrime] (n : ℕ) (hn : 1 ≤ n)
    (A₀ : Subalgebra k (Localization.AtPrime q ⧸
      (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)) [IsLocalRing A₀]
    (hA₀ : A₀.IsPopescuAdmissible ((q.map (algebraMap Λ (Localization.AtPrime q))).map
      (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n))))
    (t₀ : ℕ) (a₀ : Fin t₀ → A₀)
    (b₀ : Module.Basis (Fin t₀) (IsLocalRing.ResidueField A₀)
      (KaehlerDifferential k (IsLocalRing.ResidueField A₀)))
    (hb₀ : ∀ j, b₀ j = KaehlerDifferential.D k (IsLocalRing.ResidueField A₀)
      (IsLocalRing.residue A₀ (a₀ j)))
    (s : Λ) (hs : s ∉ q) (μ : Fin t₀ → Λ)
    (hμ : ∀ j,
      Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)
        (algebraMap Λ (Localization.AtPrime q) (μ j)) =
      (a₀ j : Localization.AtPrime q ⧸
        (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n) *
        Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)
          (algebraMap Λ (Localization.AtPrime q) s)) :
    ∃ (A : Subalgebra k (Localization.AtPrime q ⧸
        (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)) (_ : IsLocalRing A),
      A₀ ≤ A ∧
      A.IsPopescuAdmissible ((q.map (algebraMap Λ (Localization.AtPrime q))).map
        (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n))) ∧
      ∃ (N : ℕ) (_ : 1 ≤ N) (c : A),
        (c : Localization.AtPrime q ⧸
          (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n) =
          (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)
            (algebraMap Λ (Localization.AtPrime q) s)) ^ N ∧
        ∃ (t : ℕ) (xs : Fin t → Λ) (a : Fin t → A),
          (∀ j, (a j : Localization.AtPrime q ⧸
            (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n) =
            Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)
              (algebraMap Λ (Localization.AtPrime q) (xs j))) ∧
          ∃ b : Module.Basis (Fin t) (IsLocalRing.ResidueField A)
              (KaehlerDifferential k (IsLocalRing.ResidueField A)),
            ∀ j, b j = KaehlerDifferential.D k (IsLocalRing.ResidueField A)
              (IsLocalRing.residue A (a j)) := by sorry

end Algebra
