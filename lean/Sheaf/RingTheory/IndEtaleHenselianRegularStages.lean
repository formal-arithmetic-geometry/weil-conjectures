/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q134 and D4
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import Sheaf.RingTheory.IndEtaleUniverseTransport
public import Sheaf.AlgebraicGeometry.IsRegularScheme

import WeilConjectures.RingTheory.ProEtale.WeakDimension
import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.RingTheory.RegularMapAscent
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence

/-!
# Regular stages and parameter quotients of an ind-etale algebra

Source: Stacks Project, Algebra, Tags 031E and 00NQ; More on Algebra, Tag 092Q
(blueprint: lem-sfb-ind-etale-henselian-regular-stages).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace RingHom

private theorem weaklyEtale_of_across
    (B : Type u) (C : Type v) [CommRing B] [CommRing C] [Algebra B C]
    (hind : (algebraMap B C).IndEtaleAcrossUniverses) : Algebra.WeaklyEtale B C := by
  let : Algebra (ULift.{v} B) (ULift.{u} C) := ULift.algebra' B (ULift.{u} C)
  apply Algebra.WeaklyEtale.ulift_iff.mp
  apply (weaklyEtale_algebraMap_iff).mp
  exact hind.weaklyEtale

private theorem regular_fibres
    (B : Type u) (C : Type v) [CommRing B] [CommRing C] [Algebra B C]
    [Algebra.WeaklyEtale B C] [IsNoetherianRing C] (p : Ideal B) [p.IsPrime] :
    IsReduced (p.Fiber C) ∧
      (∀ (q : Ideal (p.Fiber C)) [q.IsPrime], IsField (Localization.AtPrime q)) ∧
      IsRegularRing (p.Fiber C) := by
  have : Ring.AbsolutelyFlat (p.Fiber C) :=
    .of_flat_lmul' p.ResidueField (p.Fiber C)
      (Algebra.WeaklyEtale.flat_lmul' p.ResidueField (p.Fiber C))
  have hf (q : Ideal (p.Fiber C)) [q.IsPrime] :
      IsField (Localization.AtPrime q) :=
    Ring.AbsolutelyFlat.isField_of_isLocalization_prime (p.Fiber C) q _
  let : Algebra C (p.Fiber C) := Algebra.TensorProduct.rightAlgebra
  have : IsNoetherianRing (p.Fiber C) :=
    isNoetherianRing_of_ringEquiv _ (Ideal.Fiber.algEquivAux₁ p).toRingEquiv.symm
  refine ⟨inferInstance, hf, ?_⟩
  apply isRegularRing_iff.mpr
  intro q hq
  let := (hf q).toField
  infer_instance

private theorem parameters_over_field_fibre
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsRegularLocalRing R] [IsRegularLocalRing S]
    (f : R →+* S) [IsLocalHom f] (hflat : f.Flat)
    (hfield : IsField (S ⧸ (IsLocalRing.maximalIdeal R).map f))
    (a b : List R) (hab : IsLocalRing.IsRegularSystemOfParameters (a ++ b)) :
    RingTheory.Sequence.IsRegular S (a.map f) ∧
      Nontrivial (S ⧸ Ideal.ofList (a.map f)) ∧
      IsRegularLocalRing (S ⧸ Ideal.ofList (a.map f)) := by
  classical
  let : Algebra R S := f.toAlgebra
  have : Module.Flat R S := hflat
  let J := (IsLocalRing.maximalIdeal R).map f
  have hJ : J = IsLocalRing.maximalIdeal S :=
    IsLocalRing.eq_maximalIdeal
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient J).mpr hfield)
  let : Field (S ⧸ J) := hfield.toField
  have : (IsLocalRing.maximalIdeal S).LiesOver (IsLocalRing.maximalIdeal R) :=
    ⟨(IsLocalRing.maximalIdeal_comap f).symm⟩
  have hdim := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal S)
  have hmap := IsLocalRing.map_maximalIdeal_of_surjective
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  rw [show algebraMap R S = f from rfl, hmap] at hdim
  have hd : ringKrullDim S = ringKrullDim R := by
    have hd' : ringKrullDim S = ringKrullDim R + ringKrullDim (S ⧸ J) := by
      simpa only [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, WithBot.coe_add]
        using congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hdim
    simpa only [ringKrullDim_eq_zero_of_field, add_zero] using hd'
  have hparams : IsLocalRing.IsRegularSystemOfParameters ((a ++ b).map f) := by
    constructor
    · change Ideal.ofList ((a ++ b).map f) = _
      rw [← Ideal.map_ofList]
      change (Ideal.span {x | x ∈ a ++ b}).map f = _
      rw [hab.1]
      exact hJ
    · simpa only [List.length_map] using hab.2.trans hd.symm
  have hreg := IsRegularLocalRing.isRegular_and_quotients_of_generators S
    (a ++ b).length (hab.2.trans hd.symm).symm ((a ++ b).map f) hparams
  have htake : ((a ++ b).map (⇑f)).take a.length = a.map (⇑f) := by simp
  have hquot : IsRegularLocalRing (S ⧸ Ideal.ofList (a.map f)) := by
    have hq := (hreg.2.1 a.length (by simp)).1
    rw [htake] at hq
    exact hq
  have hweak : RingTheory.Sequence.IsWeaklyRegular S (a.map f) := by
    exact (RingTheory.Sequence.isWeaklyRegular_append_iff S (a.map f) (b.map f)).mp
      (by simpa only [List.map_append] using hreg.1.toIsWeaklyRegular) |>.1
  refine ⟨?_, inferInstance, hquot⟩
  apply (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal
    (M := S) ?_).mpr hweak
  intro x hx
  rw [← hparams.1]
  exact Ideal.subset_span (by
    change x ∈ (a ++ b).map f
    simp only [List.map_append, List.mem_append]
    exact Or.inl hx)

/-- A Noetherian ind-etale algebra with nonempty connected spectrum over a regular ring is
regular and a domain. A list extending to parameters at every prime containing its ideal
is regular at each target maximal ideal, with nonzero regular local quotient, if its
extended ideal lies in every target maximal ideal. Every fibre is reduced, its prime
localizations are fields, and it is regular. Lists include the empty list.

Source: Stacks, Tags 092Q, 031E, 0569, 033N, 00ON, 00NQ and Definition 00LF
(blueprint: lem-sfb-ind-etale-henselian-regular-stages).

Proof:
1. Transport the ind-etale hypothesis to weak etaleness on the original universes.
   Weak etaleness gives flatness and is preserved by residue-field base change.
2. Apply the proved absolutely-flat multiplication criterion over each residue field.
   The fibre is absolutely flat, hence reduced, and its prime localizations are fields.
   This is the first paragraph of the proof of Stacks Tag 092Q, and avoids finite
   subalgebras and their product-of-fields decompositions.
3. Each fibre is a quotient of a localization of C, hence Noetherian. Its field local
   rings are regular, including vacuously the empty fibre. Regular-map ascent gives
   regularity of C. Its nonempty connected regular spectrum is integral, so C is a domain.
4. At a maximal m of C put p = m.comap (algebraMap B C). The induced map B_p to C_m
   is flat and local. The fibre-local-ring isomorphism identifies its closed fibre
   with a prime localization of the fibre, a field. Consequently p C_m is the maximal
   ideal of C_m, and the flat height formula gives dim C_m = dim B_p.
5. The extended parameter ideal lies in m, so its original ideal lies in p. Extend
   the list to parameters in B_p. Their images generate the maximal ideal of C_m
   and have its dimension as length. They are parameters in the regular local ring
   C_m. The regular-local-generators theorem gives regularity of the full sequence
   and of every initial quotient. Restrict to the original list. Its ideal is proper,
   giving the nonzero quotient required for regularity of the sequence. An empty list
   gives C_m itself; none of the steps requires positive length.
-/
theorem indEtale_henselian_regular_stages
    (B : Type u) (C : Type v) [CommRing B] [CommRing C] [Algebra B C]
    [IsRegularRing B] [IsNoetherianRing C] [ConnectedSpace (PrimeSpectrum C)]
    (t : List B)
    (hparameters : ∀ (p : Ideal B) [p.IsPrime], Ideal.ofList t ≤ p →
      ∃ s : List (Localization.AtPrime p),
        IsLocalRing.IsRegularSystemOfParameters
          (t.map (algebraMap B (Localization.AtPrime p)) ++ s))
    (hind : (algebraMap B C).IndEtaleAcrossUniverses)
    (hjac : ∀ (m : Ideal C) [m.IsMaximal],
      (Ideal.ofList t).map (algebraMap B C) ≤ m) :
    IsRegularRing C ∧ IsDomain C ∧
      (∀ (m : Ideal C) [m.IsMaximal],
        RingTheory.Sequence.IsRegular (Localization.AtPrime m)
          (t.map (algebraMap B (Localization.AtPrime m))) ∧
        Nontrivial (Localization.AtPrime m ⧸
          Ideal.ofList (t.map (algebraMap B (Localization.AtPrime m)))) ∧
        IsRegularLocalRing (Localization.AtPrime m ⧸
          Ideal.ofList (t.map (algebraMap B (Localization.AtPrime m))))) ∧
      (∀ (p : Ideal B) [p.IsPrime], IsReduced (p.Fiber C) ∧
        (∀ (q : Ideal (p.Fiber C)) [q.IsPrime], IsField (Localization.AtPrime q)) ∧
        IsRegularRing (p.Fiber C)) := by
  have : Algebra.WeaklyEtale B C := weaklyEtale_of_across B C hind
  have hfib := regular_fibres B C
  have hflat : (algebraMap B C).Flat := flat_algebraMap_iff.mpr inferInstance
  have hreg : IsRegularRing C :=
    isRegularRing_of_flat_of_regular_fibers hflat (fun p _ ↦ (hfib p).2.2)
  have hdom : IsDomain C := by
    have : ConnectedSpace (AlgebraicGeometry.Spec (.of C)) := by
      change ConnectedSpace (PrimeSpectrum C)
      infer_instance
    let : AlgebraicGeometry.IsRegular (AlgebraicGeometry.Spec (.of C)) :=
      ⟨fun z ↦ IsRegularLocalRing.of_ringEquiv
        (AlgebraicGeometry.Spec.stalkIso (.of C) z).commRingCatIsoToRingEquiv.symm⟩
    exact (AlgebraicGeometry.affine_isIntegral_iff (.of C)).mp
      (AlgebraicGeometry.IsRegular.isIntegral _)
  refine ⟨hreg, hdom, ?_, hfib⟩
  intro m hm
  let p := m.comap (algebraMap B C)
  have hp : p.IsPrime := Ideal.comap_isPrime _ m
  let f := Localization.localRingHom p m (algebraMap B C) rfl
  let J := (IsLocalRing.maximalIdeal (Localization.AtPrime p)).map f
  have hJ : J = (p.map (algebraMap B C)).map
      (algebraMap C (Localization.AtPrime m)) := by
    dsimp only [J]
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p, Ideal.map_map, Ideal.map_map]
    apply congrArg (fun g : B →+* Localization.AtPrime m ↦ p.map g)
    ext x
    exact Localization.localRingHom_to_map p m (algebraMap B C) rfl x
  obtain ⟨Q, hQ⟩ : ∃ Q : PrimeSpectrum (p.Fiber C),
      Q.asIdeal.comap Algebra.TensorProduct.includeRight = m := by
    let x : PrimeSpectrum.comap (algebraMap B C) ⁻¹' {⟨p, hp⟩} :=
      ⟨⟨m, inferInstance⟩, rfl⟩
    refine ⟨PrimeSpectrum.preimageEquivFiber B C ⟨p, hp⟩ x, ?_⟩
    exact congrArg (fun x ↦ x.1.asIdeal)
      ((PrimeSpectrum.preimageEquivFiber B C ⟨p, hp⟩).left_inv x)
  have transport (r s : Ideal C) [r.IsPrime] [s.IsPrime] (hrs : r = s) :
      (Localization.AtPrime r ⧸ (p.map (algebraMap B C)).map
        (algebraMap C (Localization.AtPrime r))) ≃+*
      (Localization.AtPrime s ⧸ (p.map (algebraMap B C)).map
        (algebraMap C (Localization.AtPrime s))) := by
    subst s
    exact RingEquiv.refl _
  have e : Localization.AtPrime Q.asIdeal ≃+* (Localization.AtPrime m ⧸ J) :=
    (Ideal.Fiber.algEquivAux₂ p Q.asIdeal).toRingEquiv |>.trans
      ((transport _ _ hQ).trans (Ideal.quotientEquivAlgOfEq C hJ.symm).toRingEquiv)
  have hfield : IsField (Localization.AtPrime m ⧸ J) :=
    e.symm.toMulEquiv.isField ((hfib p).2.1 Q.asIdeal)
  have htp : Ideal.ofList t ≤ p := Ideal.map_le_iff_le_comap.mp (hjac m)
  obtain ⟨s, hs⟩ := hparameters p htp
  have hlocal := parameters_over_field_fibre f (hflat.localRingHom m p rfl) hfield
    (t.map (algebraMap B (Localization.AtPrime p))) s hs
  have hmap : (t.map (algebraMap B (Localization.AtPrime p))).map f =
      t.map (algebraMap B (Localization.AtPrime m)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro x hx
    exact Localization.localRingHom_to_map p m (algebraMap B C) rfl x
  rw [hmap] at hlocal
  exact hlocal

end RingHom
