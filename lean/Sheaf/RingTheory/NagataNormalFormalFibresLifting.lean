module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import WeilConjectures.RingTheory.NagataRing
import WeilConjectures.RingTheory.FiniteOverNagata
import WeilConjectures.RingTheory.FormalFibreQuotientIso
import WeilConjectures.RingTheory.FiniteModuleComplete
import WeilConjectures.RingTheory.JapaneseDomain
import WeilConjectures.RingTheory.CompletionFiniteExtension
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Ideal-adic lifting of geometrically normal formal fibres

Source: Kurano–Shimomoto, Ideal-adic completion of quasi-excellent rings (after Gabber),
Theorem 5.1, Step 1 (1-4), p. 8; Appendix A, Definition A.1(1) and the Nagata Z-ring
row, pp. 14–15, citing Nishimura–Nishimura, Theorem A.
(blueprint: lem-per-nagata-normal-formal-fibres-lifting)
-/

@[expose] public section

universe u v

/-- Geometrically normal formal fibres lift from a Nagata closed fibre of a complete pair.
Source: Kurano–Shimomoto, Theorem 5.1, Step 1 (1-4), p. 8, and Appendix A,
Definition A.1(1), Nagata Z-ring row, pp. 14–15 (Nishimura–Nishimura, Theorem A).
(blueprint: lem-per-nagata-normal-formal-fibres-lifting)

Here `N(R)` is expanded inline: for each prime `p` of `R`, each prime `q` of `R_p`,
and each finite purely inseparable extension `k` of `κ(q)`, every prime localization
of `k ⊗[κ(q)] q.Fiber (completion(R_p))` is an integrally closed domain.
Mathlib's `q.Fiber` orders the inner tensor factors as `κ(q) ⊗[R_p] completion(R_p)`;
tensor symmetry identifies this with the order in the source statement.

Proof:
1. By lem-per-adic-nagata-lifting, `A` is Nagata. If `N(A)` fails, choose a maximal
   ideal `H` with `N(A/H)` false by the ascending chain condition. Put `R = A/H`.
   By lem-weil-pbc-finite-over-nagata-nagata, `R` is Noetherian and Nagata; all its
   nonzero proper quotients satisfy `N`. The zero ring satisfies `N` vacuously.
2. Failure supplies primes `q ≤ p` and a finite purely inseparable extension `k/κ(q)`.
   Tensor cancellation (lem-weil-pbc-tensor-cancel-base-change) and the quotient
   comparison (lem-weil-pbc-formal-fibre-quotient-iso) identify the failed test with
   an extended generic formal fibre of `(R/q)_(p/q)`. If `q ≠ 0`, maximality gives
   normality, a contradiction. Thus `R` is a domain and `q = 0`.
3. Put `J = IR`. Finite-module completeness
   (lem-weil-pbc-finite-module-complete-over-complete-noetherian) makes `R` complete
   and separated for `J`. Hence `J` is proper. If `J = 0`, `R` is finite over `A/I`,
   and lem-per-finite-algebra-normal-formal-fibres contradicts failure of `N(R)`.
4. For any finite purely inseparable extension `L/Frac(R)`, let `T` be the integral
   closure of `R` in `L`. The Nagata and Japanese definitions make `T` finite over
   `R`. By lem-weil-pbc-integral-closure-finite-extension-normal, it is a normal
   domain with fraction field `L`. Finite ascent makes it Noetherian and Nagata;
   finite-module completeness makes it complete for the nonzero proper ideal `JT`.
5. For a nonzero proper ideal `U` of `T`, choose `0 ≠ t ∈ U`. A monic equation for
   `t`, stripped of powers of its variable, has nonzero constant coefficient in
   `U ∩ R`. Thus this contraction is nonzero and proper. The quotient `T/U` is
   finite over `R/(U ∩ R)`, which satisfies `N` by maximality. Apply
   lem-per-finite-algebra-normal-formal-fibres to obtain `N(T/U)`. Now
   lem-per-normal-minimal-quotient-analytic-normality makes every completed prime
   localization of `T` a normal domain.
6. By lem-weil-pbc-completion-finite-extension, the tensor product of the completion
   of `R_p` with `T` is the finite product of the completions of `T_t` over `p`.
   Tensor with `L` over `T`; finite products commute with this tensor product.
   By lem-weil-pbc-tensor-cancel-base-change and lem-weil-pbc-localization-base-change,
   the result identifies `L ⊗[R] completion(R_p)` with a finite product of
   localizations of those normal domains. They are normal by
   lem-weil-pbc-localization-normal-domain; a zero localization is normal vacuously.
   A prime of a finite product selects one factor, and its prime localization is
   that factor's prime localization. The product is normal. Taking `L = k` from
   step 2 contradicts its failed test, proving `N(A)`. -/
theorem normal_formal_fibres_of_adically_complete
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A] (hNagata : IsNagataRing (A ⧸ I))
    (hN : ∀ (p : Ideal (A ⧸ I)) [p.IsPrime] (q : Ideal (Localization.AtPrime p)) [q.IsPrime]
        (k : Type (max u v)) [Field k] [Algebra q.ResidueField k]
        [Module.Finite q.ResidueField k] [IsPurelyInseparable q.ResidueField k],
        ∀ (s : Ideal (TensorProduct q.ResidueField k
            (q.Fiber (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
              (Localization.AtPrime p))))) [s.IsPrime],
          IsDomain (Localization.AtPrime s) ∧ IsIntegrallyClosed (Localization.AtPrime s)) :
    ∀ (p : Ideal A) [p.IsPrime] (q : Ideal (Localization.AtPrime p)) [q.IsPrime]
      (k : Type (max u v)) [Field k] [Algebra q.ResidueField k]
      [Module.Finite q.ResidueField k] [IsPurelyInseparable q.ResidueField k],
      ∀ (s : Ideal (TensorProduct q.ResidueField k
          (q.Fiber (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
            (Localization.AtPrime p))))) [s.IsPrime],
        IsDomain (Localization.AtPrime s) ∧ IsIntegrallyClosed (Localization.AtPrime s) := by
  sorry
