module

public import Sheaf.RingTheory.RotthausBoundarySystem
public import WeilConjectures.RingTheory.NagataRing
public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import WeilConjectures.RingTheory.AdicCompletionNoetherian

/-!
# Rotthaus's finite boundary criterion

Source: Kurano–Shimomoto, Ideal-adic completion of quasi-excellent rings (after Gabber),
Theorem 5.3, printed p. 11; Nishimura–Nishimura, Theorem 1.9 and Proposition 1.18.
(blueprint: lem-per-qe-rotthaus-finite-boundary)
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace RingTheory.Rotthaus

/-- Finitely many contracted normalized principal boundaries force nonzero contraction
of a minimal singular prime, assuming all semilocal contractions have positive height.
Source: Kurano–Shimomoto, Theorem 5.3, printed p. 11; Nishimura–Nishimura,
Theorem 1.9 and Proposition 1.18 (blueprint: lem-per-qe-rotthaus-finite-boundary).

Proof:
1. Suppose the contraction to `B` is zero. Then `B` embeds in the domain `C / s`.
   If `x = 0`, the semilocal completions are localizations of `B`, and their
   contracted primes must be zero, contrary to positive height. Thus `x ≠ 0`
   and `x ∉ sγ`. Completeness puts `x` in every maximal ideal by
   lem-weil-pbc-adic-complete-jacobson-radical, so `x` is a nonunit.
2. Apply lem-per-bounded-formal-singular-primes-stabilize using Noetherianity,
   Nagata, completeness, the G-ring quotient and finite boundary. Above some
   finite set γ₀ the contracted primes are extended along every transition map.
   Restriction preserves boundary finiteness; contraction compatibility follows
   from composition of the canonical maps to the local completion.
3. Apply lem-per-bounded-normalization-limit-finite to this restricted family.
   Its normalization limit `T` is finite and injective over `B`, and every prime
   minimal over `xT` contracts to the boundary union. The extension is integral
   by lem-weil-pbc-finite-algebra-is-integral.
4. Choose `P` minimal over `xB` by lem-weil-pbc-minimal-prime-over-proper-ideal.
   By lem-weil-pbc-integral-injective-lying-over lift it to `T`, then choose a
   smaller prime minimal over `xT` by lem-weil-pbc-prime-contains-minimal-prime.
   Its contraction is `P` by minimality, so Step 3 gives a γ and `Q` minimal
   over `xEγ` contracting to `P`.
5. Contract `Q` to `qγ` in `Dγ`. The identification `Dγ / xDγ = Bγ / xBγ`
   from lem-weil-pbc-adic-completion-mod-power identifies primes containing `x`
   with the relevant primes of `B`, preserving and reflecting inclusion.
   Minimality of `P` therefore makes `qγ` minimal over `xDγ`.
6. By lem-weil-pbc-localization-noetherian and
   lem-weil-pbc-adic-completion-noetherian, `Dγ` is Noetherian. Apply
   lem-sfb-krull-principal-ideal-height-bound to get height at most one.
   But `sγ` has positive height and is strictly below `qγ` because `x ∉ sγ`.
   A prime strictly below `sγ` then gives a chain of length two, a contradiction. -/
theorem finite_boundary_nonzero_contraction
    (B : Type u) [CommRing B] [IsNoetherianRing B] (hNagata : IsNagataRing B)
    (x : B) [IsAdicComplete (Ideal.span {x}) B]
    (hG : IsGRing (B ⧸ Ideal.span {x})) (n : MaximalSpectrum B)
    (s : PrimeSpectrum (LocalCompletion x n))
    (hs : ¬ IsRegularLocalRing (Localization.AtPrime s.asIdeal))
    (hmin : ∀ t : PrimeSpectrum (LocalCompletion x n),
      t.asIdeal < s.asIdeal → IsRegularLocalRing (Localization.AtPrime t.asIdeal))
    (hheight : ∀ (γ : Finset (MaximalSpectrum B)) (hn : n ∈ γ),
      0 < ringKrullDim (Localization.AtPrime (contractedPrime x n s γ hn).asIdeal))
    (hfinite : (boundary x n s).Finite) :
    s.asIdeal.comap (algebraMap B (LocalCompletion x n)) ≠ ⊥ := by
  sorry

end RingTheory.Rotthaus
