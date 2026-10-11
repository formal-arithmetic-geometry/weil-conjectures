module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Finiteness of the normalization of a finite type domain over ℤ

Source: literature/stacks-project/algebra.tex, Algebra, Proposition Tag 0335,
items (3) and (5), together with Definitions Tags 032R and 032F
(blueprint: lem-weil-pbc-finite-type-z-domain-normalization-finite).
-/

@[expose] public section

universe u v

namespace RingTheory

/--
Let `A` be an integral domain of finite type over `ℤ`, and let `K` be its field
of fractions. The integral closure of `A` in `K` is finite as an `A`-module.

Source: literature/stacks-project/algebra.tex, Algebra, Proposition Tag 0335,
items (3) and (5), with Definitions Tags 032R and 032F
(blueprint: lem-weil-pbc-finite-type-z-domain-normalization-finite).

Proof: (1) `ℤ` is Nagata, by Proposition Tag 0335 (3), using the characteristic-zero
normal-domain argument of Lemma Tag 032M. (2) Finite type algebras over a Nagata
ring are universally Japanese by Proposition Tag 0335 (5), so `A` is N-2.
(3) Apply the N-2 condition to the trivial finite extension of the fraction field;
the integral closure is finite, by Definition Tag 032F. The proof uses
`def-weil-pbc-nagata-ring`, `def-weil-pbc-noetherian-ring`,
`def-weil-pbc-japanese-domain`, `def-pc-field-extension`,
`def-weil-pbc-normal-ring`, `lem-weil-pbc-char-zero-field-extension-separable`,
`def-weil-pbc-separable-algebraic-extension`,
`lem-weil-pbc-noetherian-normal-separable-integral-closure-finite`, and
`lem-weil-pbc-nagata-universally-japanese`.
-/
theorem finiteTypeZDomain_integralClosure_finite
    (A : Type u) (K : Type v) [CommRing A] [IsDomain A]
    [Algebra.FiniteType ℤ A] [Field K] [Algebra A K]
    [IsFractionRing A K] :
    Module.Finite A (integralClosure A K) := by
  sorry

end RingTheory
