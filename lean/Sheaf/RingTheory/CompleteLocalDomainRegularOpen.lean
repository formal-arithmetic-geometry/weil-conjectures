/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Sheaf.AlgebraicGeometry.IsRegularScheme
import WeilConjectures.RingTheory.CompleteLocalDomainFiniteOverRegular
import WeilConjectures.RingTheory.RegularLocalLocalization
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Sheaf.RingTheory.NonemptyRegularOpenSeparableAscent
import WeilConjectures.FieldTheory.PurelyInseparablePthRootTower
import WeilConjectures.RingTheory.Derivation.DetectNonPthPower
import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.RingTheory.Derivation.CompletionAndLocalization
import WeilConjectures.AlgebraicGeometry.DegreePExtensionRegular
import WeilConjectures.RingTheory.LocalizationOfRegularRing
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# A nonempty regular open in the spectrum of a complete local domain

Source: Stacks Project, More on Algebra, Tag 07PI,
`lemma-complete-Noetherian-domain-J-0`, with J-0 expanded by Tag 07P7, `definition-J`
(blueprint: lem-per-complete-local-domain-regular-open).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace IsLocalRing

/-- A Noetherian local domain complete for its maximal ideal has a nonempty Zariski-open
subset of its prime spectrum on which every prime localization is regular local.

Source: Stacks Project, More on Algebra, Tag 07PI,
`lemma-complete-Noetherian-domain-J-0`, and Tag 07P7, `definition-J`
(blueprint: lem-per-complete-local-domain-regular-open).

Proof plan, following the ten steps of the DAG node:

1. By `lem-weil-pbc-complete-local-domain-finite-over-regular`, choose a complete regular
   local subring A₀ of A = R over which A is finite. It is a domain. Its localizations are
   regular by `lem-weil-pbc-regular-local-localization`, so its entire spectrum is a
   nonempty regular open (containing the zero prime). Write K₀ and K for the fraction
   fields; K/K₀ is finite by `lem-trf-finite-domain-fraction-degree`.
2. For each intermediate field M, put B(M) = A ∩ M. This is finite over A₀ by
   `lem-weil-pbc-noetherian-submodule-finite` and is Noetherian by
   `lem-weil-pbc-finite-algebra-noetherian`. Module generators also generate its algebra,
   so B(M) is of finite type over A₀.
3. By `lem-weil-pbc-finite-algebra-is-integral`, each nonzero a in A has a monic relation
   over A₀. Cancel initial powers of a until its constant coefficient c₀ is nonzero.
   The relation expresses a⁻¹ with denominator c₀, showing (A₀ ∖ {0})⁻¹A = K.
   For x in M, write x = a/s with nonzero s in A₀; then a = sx belongs to B(M).
   Thus Frac(B(M)) = M, with denominators taken in A₀.
4. By `lem-weil-pbc-separable-first-purely-inseparable`, the separable closure M₀ of K₀
   inside K is finite separable over K₀ and K/M₀ is finite purely inseparable. Apply
   `lem-exc-j0-separable-finite-type-ascent` to A₀ → B(M₀). This gives a nonempty regular
   open for B(M₀); if M₀ = K, it already proves the conclusion, including characteristic 0.
5. Otherwise the characteristic is a prime p. Use
   `lem-weil-pbc-purely-inseparable-pth-root-tower` to write K as a finite tower from M₀
   whose successive extensions adjoin α with αᵖ in the preceding field, not a pth power,
   and have degree p. Induct along this tower on B(M) having a nonempty regular open;
   step 4 is the base case.
6. At a successor step M ⊂ M(α), put B = B(M) and E = B(M(α)). Choose nonzero s in A₀
   with z = sα in E by step 3. Then b = zᵖ lies in B and is not a pth power in M.
   For C = B[z], monic division and the degree-p field extension identify
   B[T]/(Tᵖ - b) with C, and Frac(C) = Frac(E).
7. Apply `lem-weil-pbc-derivation-nonzero-on-non-pth-power` to obtain a derivation D on B
   with D(b) nonzero. Choose nonzero h in B whose principal open lies in the inductively
   supplied regular open. Set g = hD(b), which is nonzero, and S = B_g.
8. By `lem-weil-pbc-localization-noetherian`, S is Noetherian. Its prime local rings are
   the regular rings B_q with g outside q (the iterated-localization fraction maps are
   inverse), so S is regular by `def-weil-regular-scheme`. Extend D to S using
   `lem-weil-pbc-derivation-extends`. There D(b) is a unit, so
   `lem-weil-pbc-degree-p-extension-regular`, with n = p, makes S[T]/(Tᵖ - b) regular.
   Localizing the presentation of step 6 identifies this ring with C_g.
9. Choose finite A₀-module generators eⱼ of E. Since Frac(C) = Frac(E), write eⱼ = uⱼ/vⱼ
   with uⱼ, vⱼ in C and vⱼ nonzero. Their product c is nonzero (also for no generators,
   when it is 1). All generators belong to C_c, so E_c = C_c and E_gc = C_gc.
10. By `lem-weil-pbc-localization-of-regular-ring`, E_gc = C_gc is regular. The principal
    open D_E(gc) is nonempty since it contains the zero prime. By
    `lem-weil-pbc-principal-localization-open-immersion`, it is the image of Spec(E_gc).
    Its local rings are E_q by the same fraction maps as in step 8 and hence are regular
    local. This completes the induction; at its last stage B(K) = A, giving the desired U.
-/
theorem exists_nonempty_open_regular_of_complete_domain
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] :
    ∃ U : Set (PrimeSpectrum R), IsOpen U ∧ U.Nonempty ∧
      ∀ p ∈ U, IsRegularLocalRing (Localization.AtPrime p.asIdeal) := by
  sorry

end IsLocalRing
