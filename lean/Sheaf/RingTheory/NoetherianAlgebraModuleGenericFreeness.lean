/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.NoetherNormalization
import WeilConjectures.Mathlib.RingTheory.NoetherNormalization
import Sheaf.RingTheory.NoetherNormalizationOverDomain

/-!
# Noetherian generic freeness for an algebra-module pair

Source: Stacks Project, Algebra, Tag 051R, `lemma-generic-flatness-Noetherian`
(blueprint: lem-pur-noetherian-algebra-module-generic-freeness).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Module

/-- Stacks Project, Algebra, Tag 051R, `lemma-generic-flatness-Noetherian`.
(blueprint: lem-pur-noetherian-algebra-module-generic-freeness)
A finite module over a finite type algebra over a Noetherian domain becomes free over the
localized base after inverting a nonzero scalar. The basis need not be finite.

Proof, following the node's eight steps:
1. The fraction equality criterion in def-weil-pbc-module-localization-away shows that
   localization preserves exact sequences. Successive localization at f and b/f^j is
   localization at fb, for rings and modules (def-weil-ring-localization-away).
2. Localizing a basis gives a basis. A short exact sequence with free quotient splits by
   lifting its basis, so an extension of free modules is free, without a rank restriction.
3. Put K = Frac(R). By lem-zl-noether-normalization-field and
   lem-zl-noether-normalization-dimension, the nonzero generic algebra has finite dimension.
   Induct strongly on this dimension, first proving the domain-algebra case at each level.
   If the generic algebra is zero, a nonzero scalar kills its unit, and localization is zero.
4. For a domain algebra S, a nonzero scalar in the kernel kills S after localization.
   Otherwise apply lem-weil-pbc-noether-normalization-over-domain and localize the base to
   obtain a finite inclusion P = R[y_1,...,y_d] into S. The base remains Noetherian and a
   domain; lem-zl-noether-normalization-dimension identifies the number of variables with d.
5. Choose a fraction-field basis from finite P-generators of S. Its lifts give an injection
   P^r into S. The quotient N is finite over P and is killed by a nonzero polynomial g:
   multiply the denominators of the coordinates of the finitely many generators.
6. The generic fibre of P/(g) has dimension below d, unless it is zero. Indeed, a prime
   chain in the quotient lifts to a chain of nonzero primes in the polynomial domain, and
   prepending (0) increases its length. For d = 0, g is a nonzero constant generically.
7. Apply induction to N over P/(g). The localization of P^r is free on its monomials
   (def-weil-pbc-mv-polynomial-ring); split the localized exact sequence to make S free.
   Combine successive localizations using step 1 to obtain a nonzero original base scalar.
8. By lem-weil-pbc-finite-type-algebra-noetherian, B is Noetherian. Apply
   lem-weil-pbc-noetherian-module-prime-filtration to the finite B-module M. Its successive
   quotients B/q are finite type domain algebras with generic dimension at most d. Apply
   the domain case or induction, multiply the finitely many nonzero scalars (empty product
   1), and localize the filtration. Steps 1 and 2 split each extension and give a basis
   of the localization of M. -/
theorem noetherian_algebra_module_generic_freeness
    (R : Type u) (B : Type v) (M : Type w)
    [CommRing R] [IsNoetherianRing R] [IsDomain R]
    [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    [AddCommGroup M] [Module B M] [Module R M] [IsScalarTower R B M]
    [Module.Finite B M] :
    ∃ a : R, a ≠ 0 ∧ Module.Free (Localization.Away a) (LocalizedModule.Away a M) := by
  sorry

end Module
