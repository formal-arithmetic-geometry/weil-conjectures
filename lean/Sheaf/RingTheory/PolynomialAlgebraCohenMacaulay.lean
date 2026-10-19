/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import WeilConjectures.RingTheory.Depth
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
import WeilConjectures.RingTheory.DepthLeSupportDimension
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.RingTheory.FlatFiberLocalDepth
import WeilConjectures.RingTheory.FlatFiberPrimeHeight
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.Flat.Basic

/-!
# Polynomial algebras over Noetherian Cohen–Macaulay rings

Source: Stacks Project, Algebra, Tag 00ND (lemma-CM-polynomial-algebra), the ring case
of Tag 0AAI (lemma-maximal-CM-polynomial-algebra)
(blueprint: lem-trf-polynomial-algebra-cm).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace MvPolynomial

private theorem depth_eq_dimension_of_regular_local (A : Type*) [CommRing A]
    [IsRegularLocalRing A] :
    (IsLocalRing.depth (R := A) A : WithBot ℕ∞) = ringKrullDim A := by
  classical
  let d := (IsLocalRing.maximalIdeal A).spanFinrank
  have hd : ringKrullDim A = (d : WithBot ℕ∞) :=
    (IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)).symm
  obtain ⟨s, hslen, hsspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank
      (p := (IsLocalRing.maximalIdeal A : Submodule A A))
      (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
  let rs := s.toList
  have hspan : Ideal.ofList rs = IsLocalRing.maximalIdeal A := by
    simpa [Ideal.ofList, rs] using hsspan
  have hlen : rs.length = d := by simpa [rs, d] using hslen
  have hrs : IsLocalRing.IsRegularSystemOfParameters rs :=
    ⟨hspan, by rw [hlen, hd]⟩
  have hreg := (IsRegularLocalRing.isRegular_and_quotients_of_generators A d hd rs hrs).1
  have hge : (d : ℕ∞) ≤ IsLocalRing.depth (R := A) A := by
    unfold IsLocalRing.depth Ideal.depth
    split_ifs with hm
    · exact le_top
    · apply le_sSup
      refine ⟨rs, hreg, ?_, ?_⟩
      · intro x hx
        rw [← hspan]
        exact Ideal.subset_span hx
      · rw [hlen]
  apply le_antisymm
  · simpa only [Module.supportDim_self_eq_ringKrullDim] using
      IsLocalRing.depth_le_supportDim (R := A) A
  · rw [hd]
    exact WithBot.coe_le_coe.mpr hge

/-- A polynomial ring in finitely many variables over a Noetherian ring whose prime
localizations have depth equal to dimension is Noetherian, and its prime localizations
also have depth equal to dimension.

Source: Stacks Project, Algebra, Tag 00ND (lemma-CM-polynomial-algebra), the ring case
of Tag 0AAI (lemma-maximal-CM-polynomial-algebra)
(blueprint: lem-trf-polynomial-algebra-cm).

Proof. Mathlib gives the polynomial algebra a finite free, hence flat, algebra structure.
For a prime `q`, contract it to `p` and use the prime-spectrum equivalence with the fibre
prime `Q` of `p.Fiber S`. The flat-fibre depth and height formulas express the depth and
height at `q` as the sums of the corresponding quantities at `p` and `Q`. The fibre is
ring-equivalent to a finite multivariate polynomial ring over the residue field, hence is
regular by the polynomial regular-ring theorem. A regular local ring has depth equal to
its Krull dimension: choose a finite generating list of its maximal ideal, apply the
regular-sequence theorem for regular systems of parameters for the lower bound, and apply
the depth-support-dimension bound for the upper bound. Substituting this fibre equality
and the hypothesis on the base into the two formulas gives the required equality.
Noetherianity of the polynomial ring is the standard finite-variable instance.
-/
theorem isNoetherianRing_and_local_depth_eq_dimension {R : Type u} [CommRing R]
    [IsNoetherianRing R]
    (hCM : ∀ (p : Ideal R) [p.IsPrime],
      (IsLocalRing.depth (R := Localization.AtPrime p)
        (Localization.AtPrime p) : WithBot ℕ∞) =
          ringKrullDim (Localization.AtPrime p))
    (n : ℕ) :
    IsNoetherianRing (MvPolynomial (Fin n) R) ∧
      ∀ (q : Ideal (MvPolynomial (Fin n) R)) [q.IsPrime],
        (IsLocalRing.depth (R := Localization.AtPrime q)
          (Localization.AtPrime q) : WithBot ℕ∞) =
            ringKrullDim (Localization.AtPrime q) := by
  let S := MvPolynomial (Fin n) R
  have hflat : (algebraMap R S).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  refine ⟨inferInstance, ?_⟩
  intro q hq
  let p : Ideal R := q.comap (algebraMap R S)
  have hp : p.IsPrime := Ideal.IsPrime.comap (algebraMap R S)
  let e := PrimeSpectrum.preimageEquivFiber R S (⟨p, hp⟩ : PrimeSpectrum R)
  let Q := e ⟨⟨q, hq⟩, rfl⟩
  have hQ : Q.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom = q :=
    congrArg (fun t ↦ t.val.asIdeal) (e.left_inv ⟨⟨q, hq⟩, rfl⟩)
  let eF := MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) R p.ResidueField
  have : IsRegularRing (p.Fiber S) := IsRegularRing.of_ringEquiv eF.toRingEquiv.symm
  have hd := RingHom.depth_eq_add_of_flat_fiber hflat p Q.asIdeal
  have hh := RingHom.height_eq_add_of_flat_fiber hflat p Q.asIdeal
  have hspec : Q.comap Algebra.TensorProduct.includeRight.toRingHom = ⟨q, hq⟩ :=
    congrArg Subtype.val (e.left_inv ⟨⟨q, hq⟩, rfl⟩)
  have hdepth := congrArg (fun t : PrimeSpectrum S ↦
    IsLocalRing.depth (R := Localization.AtPrime t.asIdeal)
      (Localization.AtPrime t.asIdeal)) hspec
  have hd' := hdepth.symm.trans hd
  rw [hQ] at hh
  have hbase : IsLocalRing.depth (R := Localization.AtPrime p)
      (Localization.AtPrime p) = p.height := by
    apply WithBot.coe_eq_coe.mp
    exact (hCM p).trans
      (IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p))
  have hfibre : IsLocalRing.depth (R := Localization.AtPrime Q.asIdeal)
      (Localization.AtPrime Q.asIdeal) = Q.asIdeal.height := by
    apply WithBot.coe_eq_coe.mp
    exact (depth_eq_dimension_of_regular_local (Localization.AtPrime Q.asIdeal)).trans
      (IsLocalization.AtPrime.ringKrullDim_eq_height Q.asIdeal
        (Localization.AtPrime Q.asIdeal))
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q), hh]
  rw [hd', hbase, hfibre, WithBot.coe_add]

end MvPolynomial
