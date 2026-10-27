module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.RingTheory.NagataRing
import WeilConjectures.RingTheory.JapaneseDomain
import WeilConjectures.RingTheory.FiniteModuleComplete
import WeilConjectures.RingTheory.FiniteOverNagata

/-!
# Nagata lifting for complete Noetherian pairs

Source: Kurano–Shimomoto, Ideal-adic completion of quasi-excellent rings (after Gabber),
Theorem 5.1, Step 1 (1-3), printed p. 8; Appendix A, Definition A.1 and the Nagata lifting
property, printed pp. 14–15. The underlying result is Marot, Sur les anneaux universellement
japonais, Proposition 2.3, printed p. 107.
(blueprint: lem-per-adic-nagata-lifting)
-/

@[expose] public section

universe u

/-- The Nagata property lifts from the quotient of an adically complete Noetherian ring.

Source: Kurano–Shimomoto, Theorem 5.1 Step 1 (1-3) and Appendix A; Marot, Proposition 2.3,
printed p. 107 (blueprint: lem-per-adic-nagata-lifting).

Proof:
1. If a prime quotient is not N-2, choose a maximal such prime `p` by the ascending chain
   condition on ideals (`def-weil-pbc-noetherian-ring`). Then `B = A/p` is a Noetherian
   domain and every quotient of `B` by a nonzero prime is N-2. If there are no primes, the
   Nagata condition is vacuous (`def-weil-pbc-nagata-ring`).
2. Put `J = IB`. The cyclic finite module `B` is complete and separated by
   `lem-weil-pbc-finite-module-complete-over-complete-noetherian`; the module powers
   `I^n B` are `J^n`. The ring `B/J = A/(I+p)` is a quotient of the Nagata ring `A/I`, hence
   Nagata by `lem-weil-pbc-finite-over-nagata-nagata`. Separatedness of the nonzero ring
   `B` implies that `J` is proper.
3. For any finite extension `L` of `Frac(B)`, let `T` be the integral closure of `B` in `L`.
   The N-2 proper prime quotients from step 1 imply that `T` is Noetherian by
   `lem-per-japanese-quotients-noetherian-normalization`. Apply
   `lem-per-adic-noetherian-normalization-finite` to the Noetherian domain `B`, its proper
   ideal `J`, the completeness in step 2, the Nagata quotient `B/J`, and the Noetherian
   normalization `T`: it follows that `T` is finite over `B`.
4. As `L` was arbitrary, `B` is N-2 (`def-weil-pbc-japanese-domain`), a contradiction.
   Every prime quotient of `A` is therefore N-2; together with its Noetherianity this is
   `IsNagataRing A` (`def-weil-pbc-nagata-ring`). -/
theorem isNagataRing_of_isAdicComplete_quotient
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    [IsAdicComplete I A] (h : IsNagataRing (A ⧸ I)) : IsNagataRing A := by
  sorry
