/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Sheaf.RingTheory.CompleteIntersectionOverField
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.RingTheory.SyntomicPolynomialFibreComparison
import Sheaf.RingTheory.LciConormalFreeRankCodimension
import Sheaf.RingTheory.SyntomicLocalKernelIntersection

/-!
# Local kernel generators with the fibre codimension count

Source: Stacks Project, Algebra, Tags 00SY and 00SC.
(blueprint: lem-weil-pbc-syntomic-codimension-local-kernel-generators).
-/

set_option autoImplicit false

@[expose] public section

universe u v

namespace Algebra

/-- Choose local presentation-kernel generators whose number is the fibre codimension.
Source: Stacks Project, Algebra, Tag 00SY, proof of (3) implies (2), choice of the
conormal basis and Nakayama; Tag 00SC, (1) implies (4), and Tag 00P2.
(blueprint: lem-weil-pbc-syntomic-codimension-local-kernel-generators).

Proof: Set P = R[x_1,...,x_n], I = ker φ, p = q ∩ R, Q = φ⁻¹(q), k = κ(p).
Coefficient reduction and tensoring the surjection identify the fibre with
k[x_1,...,x_n]/Ibar and its canonical prime with a quotient prime t. The complete
intersection neighbourhood hypothesis transfers to this quotient. By 00SC its localized
conormal module is free of rank c = n-d, where d is the local topological dimension
at t; 00P2 gives d ≤ n. The same homeomorphism identifies d with the stated dimension
of the fibre of S. Write Qbar for the inverse-image prime in k[x_1,...,x_n]. The vector space
Ibar_Qbar / Qbar Ibar_Qbar has dimension c: it is the residue reduction of the
localized conormal module, since Ibar_Qbar is contained in Qbar. The images of I
span this vector space, so select c of those images as a basis and use their
original representatives f_i in I. Equivalently, clear denominators outside Qbar
in these selected representatives; multiplying individual basis vectors by units
preserves their linear independence and span.
Nakayama over the polynomial fibre local ring makes these c images generate Ibar
there. The polynomial local ring A = P_Q modulo pA is this polynomial fibre local
ring, so, with J = (f_i), IA ≤ JA + pA. More precisely IA ≤ JA + (IA ∩ pA).
Flatness of S_q over R_p gives IA ∩ pA = pIA by tensoring the kernel sequence;
thus IA ≤ JA + pIA. The ideal IA is finite by hfg, and pA lies in the maximal
ideal of A. Nakayama applied to IA/JA gives IA = JA. Since d ≤ n and c = n-d,
we have c ≤ n and n-c = d. For c = 0 the same argument makes IA zero; the
specified fibre prime excludes the empty fibre. No regularity of R is required. -/
theorem exists_codimension_local_kernel_generators
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) (n : ℕ) (φ : MvPolynomial (Fin n) R →ₐ[R] S)
    (hφ : Function.Surjective φ) (hfg : (RingHom.ker φ.toRingHom).FG)
    (hflat : (Localization.localRingHom (q.asIdeal.comap (algebraMap R S)) q.asIdeal
      (algebraMap R S) rfl).Flat)
    (hci : ∃ h : (q.asIdeal.comap (algebraMap R S)).Fiber S,
      h ∉ (PrimeSpectrum.preimageEquivFiber R S (q.comap (algebraMap R S))
        ⟨q, rfl⟩).asIdeal ∧
      IsGlobalCompleteIntersection (q.asIdeal.comap (algebraMap R S)).ResidueField
        (Localization.Away h)) :
    ∃ (c : ℕ) (f : Fin c → MvPolynomial (Fin n) R),
      c ≤ n ∧ Ideal.span (Set.range f) ≤ RingHom.ker φ.toRingHom ∧
      Ideal.map (algebraMap _
        (Localization.AtPrime (q.asIdeal.comap φ.toRingHom))) (Ideal.span (Set.range f)) =
      Ideal.map (algebraMap _
        (Localization.AtPrime (q.asIdeal.comap φ.toRingHom))) (RingHom.ker φ.toRingHom) ∧
      topologicalKrullDimAt
        (PrimeSpectrum.preimageEquivFiber R S (q.comap (algebraMap R S)) ⟨q, rfl⟩) =
          (n - c : ℕ) := by sorry

end Algebra
