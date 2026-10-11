module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Prime membership in a finite projective module is detected at the prime localization

Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 00NX
(blueprint: lem-sc-affine-finite-projective-prime-membership)
-/

@[expose] public section

universe u v
namespace Module

/-- Prime membership in a finite projective module is detected at the prime localization.

Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 00NX
(blueprint: lem-sc-affine-finite-projective-prime-membership)
Here `R_p = Localization.AtPrime p` [def-weil-pbc-localization-at-prime] and
`N_p = LocalizedModule p.primeCompl N` [def-weil-pbc-module-localization]; `pN_p` is the
extension of `p` to `R_p` acting on `N_p`, and `pN` is `p • ⊤`.
Proof. Step 1: since `N` is finite, choose a surjection `π : R^n → N`; the lifting clause
of [def-weil-pbc-projective-module] lifts `id_N` along `π`, giving `i : N → R^n` with
`π ∘ i = id_N`. Localizing at `p` [def-weil-pbc-module-localization] gives `i_p`, `π_p`
with `π_p ∘ i_p = id`. Step 2: if `s/1 ∈ pN_p`, applying the `R_p`-linear `i_p` gives
`i(s)/1 ∈ p(R^n)_p`; by [lem-sc-free-prime-membership] `i(s) ∈ pR^n`, and applying `π`
gives `s = π(i(s)) ∈ pN`. Conversely, if `s ∈ pN`, the canonical localization map sends
this relation to `s/1 ∈ pN_p`.
-/
theorem prime_mem_localized_iff
    {R : Type u} [CommRing R] {N : Type v} [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (s : N) (p : Ideal R) [p.IsPrime] :
    LocalizedModule.mk s 1 ∈
        (Ideal.map (algebraMap R (Localization.AtPrime p)) p) •
          (⊤ : Submodule (Localization.AtPrime p) (LocalizedModule p.primeCompl N)) ↔
      s ∈ p • (⊤ : Submodule R N) := by
  sorry

end Module
