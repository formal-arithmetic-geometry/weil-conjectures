/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Algebra
import Sheaf.RingTheory.QuasiExcellentNagata
import WeilConjectures.RingTheory.NagataRing
import WeilConjectures.RingTheory.JapaneseDomain
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct
import Mathlib.RingTheory.FiniteType
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.Ideal.GoingUp
import WeilConjectures.RingTheory.CompletionFiniteExtension

/-!
# Completion of an excellent henselian local domain

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé I, Corollary 6.3(ii),
printed p. 14; invoked in Exposé III, Proposition 3.1, printed p. 37
(blueprint: lem-per-henselian-excellent-completion-domain).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AdicCompletion

/-- The maximal-ideal-adic completion of an excellent henselian Noetherian local
integral domain is an integral domain.

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé I, Corollary 6.3(ii),
printed p. 14; Exposé III, Proposition 3.1, printed p. 37
(blueprint: lem-per-henselian-excellent-completion-domain).

Proof:
1. Let K be the fraction field of A and B its integral closure in K. Excellence
   implies quasi-excellence, hence Nagata by lem-exc-quasi-excellent-nagata.
   At the zero prime, def-weil-pbc-nagata-ring gives the Japanese condition
   def-weil-pbc-japanese-domain. Apply it to K/K to see that B is module-finite.
   By lem-weil-pbc-integral-closure-finite-extension-normal, B is a normal domain
   and A embeds into B inside K (def-weil-pbc-integral-closure).
2. By lem-weil-pbc-finite-over-henselian-local-product, B is a finite product of
   henselian local rings. Discard zero factors. There is at least one remaining
   factor since B is nonzero; two would give a nontrivial idempotent, impossible
   in a domain. Thus B is henselian local, with maximal ideal n contracting to m.
3. Finite module generators also generate B as an A-algebra
   (def-weil-pbc-finite-type-algebra). Apply
   lem-exc-finite-type-localization-excellent with multiplicative set {1} to make
   B excellent, hence Noetherian by def-exc-excellent-ring.
4. The completion clause of lem-per-henselian-normal-completion-preparation now
   applies to the normal excellent Noetherian local domain B. Its n-adic
   completion is a normal Noetherian local domain.
5. Complete the exact sequence 0 → A → B → B/A → 0 of finite A-modules.
   By lem-weil-pbc-completion-exact-finite-modules this gives an injection from
   the m-adic completion of A to the mB-adic completion of B, preserving products
   and one coordinatewise. Every prime over m is maximal by
   lem-weil-pbc-integral-prime-over-maximal-maximal; since B is local, n is the
   unique such prime. The comparison of lem-weil-pbc-completion-finite-extension
   identifies the mB-adic completion with the n-adic completion of B. Localizing
   A at m and B at n changes neither ring, since only units are inverted.
6. The resulting injective unital ring map from the completion of A into a domain
   shows that one is nonzero and that a product is zero only if a factor is zero.
-/
theorem isDomain_of_henselian_excellent (A : Type u) [CommRing A]
    [HenselianLocalRing A] [IsNoetherianRing A] [IsDomain A] (hA : IsExcellent A) :
    IsDomain (AdicCompletion (IsLocalRing.maximalIdeal A) A) := by
  sorry

end AdicCompletion
