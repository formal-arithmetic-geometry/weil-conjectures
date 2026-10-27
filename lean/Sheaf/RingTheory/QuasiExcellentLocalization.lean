/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso
import WeilConjectures.RingTheory.AdicCompletionRingEquiv
import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.RegularRingEquiv
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.RingHom.EssFiniteType
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Localization preserves quasi-excellence

Source: Stacks Project, More on Algebra, Tag 07QU, lemma-finite-type-over-excellent,
applied to the identity finite type algebra (blueprint: lem-per-quasi-excellent-localization).
-/

@[expose] public section

set_option autoImplicit false

universe u

/-- Localization at any multiplicative subset preserves quasi-excellence, including
localization at `{1}` and at a subset containing zero. The carrier is the localization
of the module `R`, equipped with Mathlib's standard commutative ring structure.

Source: Stacks Project, More on Algebra, Tag 07QU, lemma-finite-type-over-excellent;
Tags 07QT, 07GH and 07P7 give the three defining conditions.
(blueprint: lem-per-quasi-excellent-localization).

Proof:
1. Put A = T⁻¹R. By def-exc-excellent-ring, R is Noetherian, a G-ring and J-2.
   The fractions of def-weil-pbc-module-localization satisfy the localization axioms:
   denominators become units, every element is a fraction, and a numerator mapping
   to zero is killed by a denominator. By lem-weil-pbc-localization-noetherian,
   A is Noetherian.
2. For a prime q of A with contraction p in R, clauses (1)--(3) of
   lem-weil-pbc-localization-prime-residue-field-iso give the canonical equivalence
   R_p ≃ A_q carrying maximal ideals to maximal ideals. By
   lem-weil-pbc-adic-completion-ring-equiv it extends to a completion equivalence
   commuting with the canonical maps. The completion map for R_p is regular by
   def-weil-pbc-g-ring. Transport regularity across this square using
   lem-weil-pbc-regular-ring-map-ring-equiv. Thus the completion map for every A_q
   is regular, so A is a G-ring.
3. For any finite type A-algebra B, both R → A and A → B are essentially of finite
   type by def-weil-pbc-essentially-finite-type-algebra: use R and T for the first
   presentation, B and {1} for the second. By
   lem-weil-pbc-essentially-finite-type-composition, B is a localization W⁻¹C of
   a finite type R-algebra C, compatibly with the R-algebra structures. The units,
   fractions and kernel conditions transport through this presentation. By the
   J-2 condition in def-exc-excellent-ring, the regular locus U in Spec C is open.
4. The contraction map h : Spec B → Spec C is continuous by
   lem-weil-pbc-localization-spectrum-embedding. At every prime b, clause (2) of
   lem-weil-pbc-localization-prime-residue-field-iso identifies C_(h(b)) and B_b.
   Applying lem-trf-regular-local-ring-isomorphism in both directions identifies
   the regular locus of B with h⁻¹(U). It is open. This proves J-2 for A.
5. Steps 1, 2 and 4 are exactly quasi-excellence by def-exc-excellent-ring. No step
   assumes finite generation of T, universal catenarity or a ground field. If
   zero belongs to T, def-weil-pbc-module-localization makes A the zero ring;
   its unital algebras are zero, so the prime-indexed conditions are vacuous and
   Step 1 still applies. Taking T = {1} also requires no change. -/
theorem isQuasiExcellent_localizedModule (R : Type u) [CommRing R]
    (hR : IsQuasiExcellent R) (T : Submonoid R) :
    IsQuasiExcellent (LocalizedModule T R) := by
  sorry
