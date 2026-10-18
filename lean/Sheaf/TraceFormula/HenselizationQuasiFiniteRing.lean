/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.RingTheory.GeneralizedHenselizationAtPrime
public import WeilConjectures.RingTheory.QuasiFiniteAtPrime
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
import Sheaf.TraceFormula.HenselizationPrimeIndEtale
import Sheaf.RingTheory.HenselianFiniteTypeProductDecomposition
import WeilConjectures.RingTheory.FiniteLocalHenselian
import Sheaf.RingTheory.IndEtaleStability
import Sheaf.RingTheory.MapIntoHenselianColimit
import Sheaf.RingTheory.QuasiFiniteFourRings
import Sheaf.RingTheory.IndEtaleUniverseTransport
import WeilConjectures.Mathlib.RingTheory.Henselian

/-!
# Ordinary henselization under a quasi-finite local map

Source: Stacks Project, Algebra, Tag 05WP, Lemma quasi-finite-henselization
(lines 43580--43615) (blueprint: lem-trf-henselization-quasi-finite-ring).
-/

@[expose] public section
set_option autoImplicit false

universe u v w z

open scoped TensorProduct

namespace Algebra

/-- Ordinary henselization comparison for a quasi-finite ring map.

Source: Stacks Project, Algebra, Tag 05WP, Lemma quasi-finite-henselization
(lines 43580--43615) (blueprint: lem-trf-henselization-quasi-finite-ring).

Proof. (1) Put `R = Aₚʰ` and `H' = B_qʰ`. The universal property in
[def-weil-pbc-henselization-at-prime] gives the canonical local map `h : R → H'`,
compatible with `A → B` and with the residue-field map. Form the tensor product of `R`
with `B_q` over `Aₚ`; the residue evaluation has a prime kernel `n`, whose contractions
to the two factors are their maximal ideals. (2) Apply
[lem-weil-pbc-quasi-finite-four-rings] to the original map and this tensor square. The
symmetry of the tensor product supplies the required surjection, and
[def-weil-pbc-ring-map-quasi-finite-at-prime] supplies finite type; hence the map to the
tensor product is quasi-finite at `n`. (3) Apply
[lem-weil-pbc-henselian-finite-type-product-decomposition]. The factor containing `n` is
finite and local over `R`; the quotient of its residue by the maximal ideal is a finite
domain over the residue field and therefore a field. By
[lem-weil-pbc-finite-local-henselian] this factor is henselian. (4) The target
henselization and this factor are ind-etale over `B`: use
[lem-trf-henselization-prime-ind-etale], [lem-weil-pbc-ind-etale-stability], and the
principal-localization presentation supplied by
[lem-weil-pbc-etale-algebra-finite-presentation-localization], together with
[def-weil-pbc-ind-etale-algebra] and [def-weil-pbc-category-colimit]. (5) The tensor
map to the target henselization factors through the localization at `n`. The uniqueness
statement [lem-weil-pbc-map-into-henselian-colimit], using
[def-weil-pbc-henselian-terminology], gives inverse local maps; their residue maps are
the identity, so they are inverse. (6) Elements outside `q` are already units in `B_q`,
so the localization is canonically the localization of `Aₚʰ ⊗_{Aₚ} B_q` at `n`.
The resulting comparison is compatible with both factors, and the finite-local property
of the selected factor gives the asserted finiteness and locality. -/
theorem henselization_quasiFinite_ring
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B]
    (p : Ideal A) [p.IsPrime] (q : PrimeSpectrum B) [q.asIdeal.LiesOver p]
    (hq : Algebra.IsQuasiFiniteAtPrime A B q)
    (H : Type w) [CommRing H]
    [Algebra (Localization.AtPrime p) H] [HenselianLocalRing H]
    (hH : Algebra.IsHenselizationAtPrime' A p H)
    (K : Type z) [CommRing K]
    [Algebra (Localization.AtPrime q.asIdeal) K] [HenselianLocalRing K]
    (hK : Algebra.IsHenselizationAtPrime' B q.asIdeal K)
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q.asIdeal)]
    [Localization.AtPrime.IsLiesOverAlgebra p q.asIdeal] :
    ∃ (h : H →+* K),
      IsLocalHom h ∧
      h.comp ((algebraMap (Localization.AtPrime p) H).comp
        (algebraMap A (Localization.AtPrime p))) =
        (algebraMap (Localization.AtPrime q.asIdeal) K).comp
          ((algebraMap B (Localization.AtPrime q.asIdeal)).comp (algebraMap A B)) ∧
      @Module.Finite H K _ _ h.toModule ∧
      ∃ (n : Ideal (TensorProduct (Localization.AtPrime p) H
          (Localization.AtPrime q.asIdeal))) (hn : n.IsPrime),
        ∃ e : K ≃+* @Localization.AtPrime _ _ n hn,
          n.comap
              ((Algebra.TensorProduct.includeLeft : H →ₐ[Localization.AtPrime p]
                TensorProduct (Localization.AtPrime p) H
                  (Localization.AtPrime q.asIdeal)).toRingHom) =
              IsLocalRing.maximalIdeal H ∧
          n.comap
              ((Algebra.TensorProduct.includeRight : Localization.AtPrime q.asIdeal →ₐ[
                Localization.AtPrime p]
                TensorProduct (Localization.AtPrime p) H
                  (Localization.AtPrime q.asIdeal)).toRingHom) =
              IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) ∧
          (∀ x : H,
            e (h x) =
              @algebraMap (TensorProduct (Localization.AtPrime p) H
                (Localization.AtPrime q.asIdeal)) (@Localization.AtPrime _ _ n hn) _ _ _
                ((Algebra.TensorProduct.includeLeft : H →ₐ[Localization.AtPrime p]
                  TensorProduct (Localization.AtPrime p) H
                    (Localization.AtPrime q.asIdeal)) x)) ∧
          (∀ y : Localization.AtPrime q.asIdeal,
            e (algebraMap (Localization.AtPrime q.asIdeal) K y) =
              @algebraMap (TensorProduct (Localization.AtPrime p) H
                (Localization.AtPrime q.asIdeal)) (@Localization.AtPrime _ _ n hn) _ _ _
                ((Algebra.TensorProduct.includeRight : Localization.AtPrime q.asIdeal →ₐ[
                  Localization.AtPrime p]
                  TensorProduct (Localization.AtPrime p) H
                    (Localization.AtPrime q.asIdeal)) y)) := by
  sorry

end Algebra
