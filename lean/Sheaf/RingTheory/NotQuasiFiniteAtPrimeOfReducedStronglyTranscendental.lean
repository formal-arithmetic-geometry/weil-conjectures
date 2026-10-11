/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.RingTheory.Algebraic.StronglyTranscendental
public import Sheaf.RingTheory.QuasiFiniteAtPrime

/-!
# Strong transcendence prevents quasi-finiteness for reduced rings

Source: Stacks Project, Algebra, Lemma 10.123.10 (Tag 00Q2)
(blueprint: lem-weil-pbc-reduced-strongly-transcendental-not-quasi-finite).
-/

@[expose] public section

universe u v

namespace Algebra

/-- (blueprint: lem-weil-pbc-reduced-strongly-transcendental-not-quasi-finite)
Stacks Project, Algebra, Lemma 10.123.10 (Tag 00Q2). For an inclusion of reduced rings,
strong transcendence of `x` and module finiteness over `R[x]` prevent quasi-finiteness
at every prime. `FaithfulSMul R S` expresses injectivity of the structure map;
`Algebra.adjoin R {x}` is `R[x]`. The finite-type instance is derived from finiteness,
using finite generation of the singleton subalgebra and transitivity of finite type.

Proof, following the five steps of the node:
1. Given a prime `q`, choose a minimal prime `q'` contained in it by
`lem-weil-pbc-prime-contains-minimal-prime`. Put `p' = q' ∩ R`. The induced map
`R/p' → S/q'` is injective, and both quotient rings are domains.
2. By `lem-weil-pbc-strongly-transcendental-quotient-minimal-prime`, the image of `x`
is strongly transcendental over `R/p'`.
3. Reduce a finite set of module generators modulo `q'`. Surjectivity of the quotient
map makes these generators span `S/q'` over `(R/p')[x]`. Together with `x`, the
original module generators also generate `S` as an `R`-algebra, proving finite type.
4. Apply `lem-weil-pbc-domains-strongly-transcendental-not-quasi-finite` to the quotient
domains. Their map is not quasi-finite at the prime `q/q'`.
5. The quotient square commutes, and `S ⊗[R] (R/p') → S/q'` is surjective because
`S → S/q'` is surjective. If the original map were quasi-finite at `q`,
`lem-weil-pbc-quasi-finite-four-rings` would make the quotient map quasi-finite at
`q/q'`, contradicting step 4. Since `q` was arbitrary, this proves the conclusion. -/
theorem not_isQuasiFiniteAtPrime_of_reduced_isStronglyTranscendental
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsReduced R] [IsReduced S] [Algebra R S] [FaithfulSMul R S]
    (x : S) (hx : IsStronglyTranscendental R x)
    [Module.Finite (Algebra.adjoin R ({x} : Set S)) S] :
    ∀ q : PrimeSpectrum S,
      ¬ @IsQuasiFiniteAtPrime R S _ _ _
        (Algebra.FiniteType.trans
          (Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton x))
          (inferInstance : Algebra.FiniteType (Algebra.adjoin R ({x} : Set S)) S)) q := by
  sorry

end Algebra
