/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Smooth.Kaehler
import Sheaf.RingTheory.KaehlerDifferentialsModPowerIdeal

/-! # Conormal residue kernel comparison
Source: Stacks Project, Algebra, Tag 02HT, proof of (4) implies (1).
-/

@[expose] public section

universe u

namespace Algebra

/-- A section at a truncation satisfying the Artin--Rees bound detects the residue kernel.

Source: Stacks Project, Algebra, Tag 02HT, proof of (4) implies (1), paragraphs
beginning "Consider the presentation" through "Since a split injection", specialized
to reduction modulo the maximal ideal (https://stacks.math.columbia.edu/tag/02HT).
(blueprint: lem-weil-pbc-truncated-section-conormal-residue-kernel).

Proof in words:
Put C = P.Ring, J = P.ker, m = maximalIdeal C, n = maximalIdeal S, and k = S/n.
The surjection C -> S identifies S with C/J, pulls n back to m, and maps m onto n.
Set E = C/(J^2 + m^N) and F = C/(J + m^N). Its kernel K has square zero.
The given R-algebra section sigma of E -> F gives a retraction of
K -> F tensor_E Omega(E/R) by retractionOfSectionOfKerSqZero_comp_kerToTensor.
The retraction is F-linear: the action on K is independent of a lift from F,
since K^2 = 0; in particular the section gives that same action.
The quotient F -> k exists because J + m^N is contained in m. Tensor the
retraction over F with k. The resulting conormal map is a split injection.

The natural surjection J -> K has kernel J^2 + (m^N intersect J), by the modular
law, since J^2 is contained in J. Consequently its reduction over k is
J/(J^2 + (m^N intersect J) + mJ). The hypothesis hAR says m^N intersect J is
contained in mJ (m^N times top is m^N as a submodule of C), so this quotient is
J/(J^2 + mJ), canonically (P.Cotangent)/(n times P.Cotangent).
No Noetherian hypothesis is needed at this step; all of Artin--Rees is hAR.

For the other side, let D = C/J^2 and let m_D be the image of m in D. Then
E = D/(m_D)^N and k is a quotient of D/m_D. Apply the differential-mod-power
lemma to D, m_D, N-1 (positive because N >= 2) and then base change to k.
This identifies k tensor_E Omega(E/R) with k tensor_D Omega(D/R).
Apply the same lemma to C, J, exponent 1, and then base change C/J -> k;
it identifies this with k tensor_C Omega(C/R). Tensor cancellation identifies
the latter with (P.CotangentSpace)/(n times P.CotangentSpace).
Every identification is induced by a quotient map or tensor cancellation.
On a class represented by j in J the composite sends j to 1 tensor dj,
which is P.cotangentComplex_mk followed by reduction. These classes span the
source, so this identifies the split injection with the reduced cotangent map.
Its injectivity says that if P.cotangentComplex x is in n times the target,
then the class of x modulo n is zero, exactly the asserted membership.

For J = 0 the source is zero and the claim is immediate; N = 2 is allowed
and uses exponent 1 in both differential comparisons. The Artin--Rees bound
is essential: without it, e.g. J = (t^2) in k[t]_(t) at N = 2, reduction of
the kernel of E -> F need not identify with J/(J^2 + mJ). -/
theorem truncated_section_conormal_residue_kernel
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing S] (P : Extension.{u} R S) [IsLocalRing P.Ring]
    (N : ℕ) (hN : 2 ≤ N)
    (hAR : ((IsLocalRing.maximalIdeal P.Ring) ^ N •
        (⊤ : Submodule P.Ring P.Ring) ⊓ P.ker) ≤
      (IsLocalRing.maximalIdeal P.Ring) • P.ker)
    (σ : (P.Ring ⧸ (P.ker ⊔ IsLocalRing.maximalIdeal P.Ring ^ N)) →ₐ[R]
        (P.Ring ⧸ (P.ker ^ 2 ⊔ IsLocalRing.maximalIdeal P.Ring ^ N)))
    (hσ : (Ideal.Quotient.factorₐ R
        (sup_le_sup (Ideal.pow_le_self (by decide : 2 ≠ 0)) le_rfl)).comp σ =
      AlgHom.id R _) :
    ∀ x : P.Cotangent,
      P.cotangentComplex x ∈
          (IsLocalRing.maximalIdeal S) • (⊤ : Submodule S P.CotangentSpace) →
        x ∈ (IsLocalRing.maximalIdeal S) • (⊤ : Submodule S P.Cotangent) := by sorry

end Algebra
