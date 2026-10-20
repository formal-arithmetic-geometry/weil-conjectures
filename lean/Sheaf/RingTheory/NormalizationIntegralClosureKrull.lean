module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.RingTheory.InjectivePiLocalizationAssociatedPrimes
import WeilConjectures.RingTheory.IntegralClosureFiniteNormalProduct
import WeilConjectures.RingTheory.JapaneseDomain
import WeilConjectures.RingTheory.KrullAkizukiNoetherian
import WeilConjectures.RingTheory.NagataOfCompleteLocal
import Sheaf.RingTheory.NormalDomainPrincipalQuotientAssociatedHeight
import Sheaf.RingTheory.NormalizationPrincipalHeightOneRefinement
import Sheaf.TraceFormula.NormalizationFiniteLocalModel
import Sheaf.TraceFormula.NormalizationFinitePrimeFibres
import WeilConjectures.AlgebraicGeometry.Regular

/-!
# Mori–Nagata normalization is Krull

Source: Swanson–Huneke, *Integral Closure of Ideals, Rings, and Modules*,
Theorem 4.10.5 and Definition 4.10.1, printed pp. 89–91
(blueprint: lem-trf-normalization-integral-closure-krull).
-/


@[expose] public section

set_option autoImplicit false

universe u

namespace RingTheory

/-- The canonical map from a localization at a prime of a domain to its fraction ring.

Source: Swanson–Huneke, Theorem 4.10.5, Definition 4.10.1, printed pp. 89–91
(blueprint: lem-trf-normalization-integral-closure-krull).
-/
noncomputable def normalizationLocalizationMap
    (A : Type u) [CommRing A] (hA : IsDomain A)
    (P : Ideal A) (hP : P.IsPrime) :
    @Localization.AtPrime A _ P hP →+* FractionRing A := by
  letI : IsDomain A := hA
  letI : P.IsPrime := hP
  exact IsLocalization.map (M := P.primeCompl)
    (T := nonZeroDivisors A) (FractionRing A) (RingHom.id A)
    (by
      intro x hx
      change x ∈ nonZeroDivisors A
      exact P.primeCompl_le_nonZeroDivisors hx)

/-- The index type of nonzero height-one prime ideals.

Source: Swanson–Huneke, Definition 4.10.1, printed p. 89
(blueprint: lem-trf-normalization-integral-closure-krull).
-/
def normalizationHeightOneIndex (A : Type u) [CommRing A] :=
  {P : Ideal A //
    P.IsPrime ∧ P ≠ ⊥ ∧ ∀ Q : Ideal A, Q.IsPrime → Q < P → Q = ⊥}

/-- Mori–Nagata: the integral closure `N` of a Noetherian domain `R` in `K = Frac R` is a
Krull domain: (i) every nonzero height-one localization is a Noetherian normal domain, (ii) `N`
is the intersection of these localizations inside `Frac N`, (iii) every nonzero element lies in
only finitely many height-one primes. An empty intersection is the whole fraction field.

Source: Swanson–Huneke, *Integral Closure of Ideals, Rings, and Modules*, Theorem 4.10.5
(Mori–Nagata), printed pp. 90–92, specialized to a domain; Definition 4.10.1, printed p. 89.

Proof (the DAG proof, step by step):
1. `Frac N = K` since `R ⊆ N ⊆ K`. For a height-one prime `Q` of `N`,
   lem-trf-normalization-finite-local-model gives a one-dimensional Noetherian local domain
   `C_p ⊆ K` with integral closure `N_Q`; Krull–Akizuki (lem-sc-krull-akizuki-noetherian)
   makes `N_Q` Noetherian, and lem-sbc-integral-closure-finite-normal-product makes it
   normal. This is clause (i).
2. For `0 ≠ x = a/d ∈ N`, a height-one `Q ∋ x` has `Q ∩ R ∈ Ass_R(R/aR)`
   (lem-trf-normalization-height-one-associated-contraction), a finite set
   (lem-weil-pbc-noetherian-associated-primes-finite); each fibre is finite
   (lem-trf-normalization-finite-prime-fibres). This is clause (iii).
3. Clause (ii) reduces to `R` local: localization at a maximal ideal `m` keeps `R` Noetherian,
   `(R∖m)⁻¹N` is its normalization (lem-weil-pbc-integral-closure-commutes-localization), and
   its height-one primes and their localizations are those of `N` disjoint from `R∖m`.
4. For local `R`, lem-trf-normalization-completed-product-comparison writes
   `N = {x ∈ K : j_i(x) ∈ T_i ∀ i}` with `T_i` the normalization of the complete local
   domain `B_i = R̂/q_i`; `B_i` is Nagata (lem-weil-pbc-complete-local-nagata), so `T_i` is
   finite over `B_i` (def-weil-pbc-japanese-domain) and Noetherian
   (lem-weil-pbc-finite-type-algebra-noetherian).
5. `T_i` is normal (lem-sbc-integral-closure-finite-normal-product,
   lem-weil-pbc-normal-domain-of-local-normal); associated primes of `T_i/bT_i` have height
   one (lem-weil-pbc-normal-domain-principal-quotient-associated-height); by
   lem-weil-pbc-module-injects-localizations-associated-primes, `T_i` is the intersection of
   its height-one localizations, each a DVR (lem-sc-normal-dim1-dvr).
6. The DVR valuations restricted to `K` give `N = {0} ∪ {x : v_λ(x) ≥ 0 ∀ λ}`, each nonzero
   element of `N` has positive value at finitely many `λ`
   (lem-sc-finite-minimal-primes-over-ideal); trivial valuations are discarded, and the
   centres `p_λ` are nonzero primes.
7. For a multiplicative `S ⊆ N∖{0}`, `S⁻¹N` is the intersection over the `λ` with
   `v_λ(S) = 0`, by explicit denominator clearing; for `S = N∖P` these are `p_λ ⊆ P`.
8. For `0 ≠ b ∈ N` and the finite `F = {λ : v_λ(b) > 0}`, `bN = ⋂_{λ∈F} J_λ` with
   `J_λ = {a : v_λ(a) ≥ v_λ(b)}`.
9. Each `J_λ` is `p_λ`-primary with `p_λ^{v_λ(b)} ⊆ J_λ`; merging equal radicals and deleting
   redundant terms gives an irredundant `bN = J_1 ∩ ⋯ ∩ J_t`.
10. lem-trf-normalization-principal-height-one-refinement: every prime containing a nonzero
   `c ∈ N` contains a height-one prime containing `c`.
11. If `p_1` is not height one, some retained `μ` has `p_μ ⊆ p_1` and `v_μ(b) = 0`; otherwise
   `N_{p_1}[1/b] = K` and all (finitely many) height-one primes below `p_1` contain `b`.
12. Prime avoidance gives `x ∈ p_1` outside those height-one primes, contradicting Step 10;
   so `μ` exists and `P = p_μ` is a nonzero prime with `b ∉ P`.
13. With `h` least such that `p_1^h ∩ J_2 ∩ ⋯ ∩ J_t ⊆ bN`, pick
   `c ∈ p_1^{h-1} ∩ J_2 ∩ ⋯ ∩ J_t` outside `bN`; then `c p_1 ⊆ bN` and `z = c/b ∉ N`.
14. `zP ⊆ P`, so `z^n d ∈ N` for a nonzero `d ∈ P` and all `n`, whence every `v_λ(z) ≥ 0` and
   `z ∈ N`, a contradiction: every `p_j` has height one.
15. Localizing at the incomparable `p_i` gives `bN_{p_i} = (J_i)_{p_i}` and
   `J_i = N ∩ (J_i)_{p_i}`; hence `a/b` in every height-one localization lies in `N`. This
   is clause (ii) for local `R` (empty decompositions cover units and fields).
16. For general `R`, `x` in every `N_Q` lies in every `(R∖m)⁻¹N`, so
   `{r : r x ∈ N}` is not proper and `x ∈ N`. With no height-one primes this gives `N = K`.

The cited statement dependencies provide the Noetherian, integral closure, localization and
normal-ring notions (blueprint: lem-trf-normalization-integral-closure-krull).
-/
theorem normalization_integralClosure_isKrull
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] :
    ∃ hN : IsDomain (integralClosure R (FractionRing R)),
      (∀ (P : Ideal (integralClosure R (FractionRing R)))
          (hP : P.IsPrime),
          P ≠ ⊥ →
            (∀ Q : Ideal (integralClosure R (FractionRing R)),
              Q.IsPrime → Q < P → Q = ⊥) →
            IsNoetherianRing (@Localization.AtPrime
              (integralClosure R (FractionRing R)) _ P hP) ∧
              IsDomain (@Localization.AtPrime
                (integralClosure R (FractionRing R)) _ P hP) ∧
              IsIntegrallyClosed (@Localization.AtPrime
                (integralClosure R (FractionRing R)) _ P hP)) ∧
      (Set.range (algebraMap (integralClosure R (FractionRing R))
          (FractionRing (integralClosure R (FractionRing R)))) =
        ⋂ s : normalizationHeightOneIndex
          (integralClosure R (FractionRing R)),
          Set.range (normalizationLocalizationMap
            (integralClosure R (FractionRing R)) hN s.1 s.2.1)) ∧
      (∀ x : integralClosure R (FractionRing R), x ≠ 0 →
        Set.Finite {P : Ideal (integralClosure R (FractionRing R)) |
          ∃ hP : P.IsPrime,
            P ≠ ⊥ ∧
              (∀ Q : Ideal (integralClosure R (FractionRing R)),
                Q.IsPrime → Q < P → Q = ⊥) ∧ x ∈ P}) := by
  sorry

end RingTheory

end
