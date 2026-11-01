/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.ProfiniteTestObjectFunctor
import all WeilConjectures.ProperBaseChange.ProfiniteTestObjectFunctor
import all Mathlib.Topology.Connected.TotallyDisconnected
import all WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import all WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale

/-!
# The profinite basis over a separably closed field

Source: Bhatt--Scholze, Examples 4.1.10 and 4.2.11; Stacks Tags 092Q, 096D, 096T.
(blueprint: lem-weil-pbc-geometric-field-profinite-dense-subsite).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace TestLC
variable {A : Type v} {B : Type w} [CommRing A] [CommRing B] [Algebra A B] (S : Profinite.{u})
private noncomputable def projection (φ : LocallyConstant S A →+* B) : C(PrimeSpectrum B, S) :=
  ⟨fun p ↦ ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := A)).symm
      (PrimeSpectrum.comap φ p)).1,
    continuous_fst.comp
      ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := A)).symm.continuous.comp
        (PrimeSpectrum.continuous_comap φ))⟩
private lemma localization_eq (φ : LocallyConstant S A →ₐ[A] B)
    (p : PrimeSpectrum B) (g : LocallyConstant S A) :
    algebraMap B (Localization.AtPrime p.asIdeal) (φ g) =
      algebraMap B (Localization.AtPrime p.asIdeal)
        (algebraMap A B (g (projection S φ.toRingHom p))) := by
  classical
  let s := projection S φ.toRingHom p
  let q := ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := A)).symm
    (PrimeSpectrum.comap φ.toRingHom p)).2
  have hp : PrimeSpectrum.comap φ.toRingHom p = LocallyConstant.toPrimeSpectrum (s, q) :=
    ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := A)).apply_symm_apply _).symm
  let χ := LocallyConstant.charFn A (g.isLocallyConstant.isClopen_fiber (g s))
  have hχ : φ χ ∉ p.asIdeal := by
    change χ ∉ (PrimeSpectrum.comap φ.toRingHom p).asIdeal
    rw [hp, LocallyConstant.mem_toPrimeSpectrum_asIdeal]
    simpa [χ, LocallyConstant.charFn_apply_of_mem] using q.isPrime.one_notMem
  have hid : IsIdempotentElem χ := by
    change χ * χ = χ
    ext x
    by_cases hx : g x = g s
    · simp [χ, LocallyConstant.charFn_apply_of_mem, hx]
    · simp [χ, LocallyConstant.charFn_apply_of_notMem, hx]
  have hχloc : algebraMap B (Localization.AtPrime p.asIdeal) (φ χ) = 1 :=
    (hid.map φ.toRingHom).algebraMap_localization_atPrime_of_notMem hχ
  have hmul : χ * g = χ * algebraMap A (LocallyConstant S A) (g s) := by
    ext x
    change χ x * g x = χ x * g s
    by_cases hx : g x = g s
    · simp [hx]
    · simp [χ, LocallyConstant.charFn_apply_of_notMem, hx]
  have h := congrArg (fun v ↦ algebraMap B (Localization.AtPrime p.asIdeal) (φ v)) hmul
  simpa only [map_mul, φ.commutes, hχloc, one_mul] using h
private noncomputable def fromIntegers (φ : LocallyConstant S ℤ →+* B) :
    LocallyConstant S A →ₐ[A] B :=
  { LocallyConstant.liftPrimeSpectrum (algebraMap A B) (projection S φ) with
    commutes' := LocallyConstant.liftPrimeSpectrum_algebraMap _ _ }
private noncomputable def toIntegers (φ : LocallyConstant S A →ₐ[A] B) :
    LocallyConstant S ℤ →+* B :=
  φ.toRingHom.comp (LocallyConstant.mapRingHom (Int.castRingHom A))
private lemma projection_toIntegers (φ : LocallyConstant S A →ₐ[A] B) (p : PrimeSpectrum B) :
    projection S (toIntegers S φ) p = projection S φ.toRingHom p := by
  obtain ⟨⟨s, q⟩, hq⟩ := LocallyConstant.toPrimeSpectrum_surjective
    (PrimeSpectrum.comap φ.toRingHom p)
  have hZ : PrimeSpectrum.comap (toIntegers S φ) p =
      LocallyConstant.toPrimeSpectrum (s, PrimeSpectrum.comap (Int.castRingHom A) q) := by
    rw [toIntegers, PrimeSpectrum.comap_comp_apply, ← hq]
    ext f
    rfl
  change ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm _).1 =
    ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := A)).symm _).1
  rw [hZ, ← hq]
  change ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm
    ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)) (s, _))).1 =
    ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := A)).symm
    ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := A)) (s, _))).1
  simp only [Homeomorph.symm_apply_apply]
private lemma from_to (φ : LocallyConstant S A →ₐ[A] B) :
    fromIntegers S (toIntegers S φ) = φ := by
  ext g
  apply PrimeSpectrum.eq_of_forall_algebraMap_localization_eq
  intro p
  change algebraMap B (Localization.AtPrime p.asIdeal)
    (LocallyConstant.liftPrimeSpectrum _ _ g) = _
  rw [LocallyConstant.algebraMap_localization_liftPrimeSpectrum,
    projection_toIntegers, localization_eq]
private lemma to_from (φ : LocallyConstant S ℤ →+* B) :
    toIntegers S (fromIntegers (A := A) S φ) = φ := by
  ext g
  apply PrimeSpectrum.eq_of_forall_algebraMap_localization_eq
  intro p
  change algebraMap B (Localization.AtPrime p.asIdeal)
    (LocallyConstant.liftPrimeSpectrum _ _
      (LocallyConstant.mapRingHom (Int.castRingHom A) g)) = _
  rw [LocallyConstant.algebraMap_localization_liftPrimeSpectrum]
  rw [show algebraMap B (Localization.AtPrime p.asIdeal) (φ g) =
    algebraMap B (Localization.AtPrime p.asIdeal)
      (g (projection S φ p) : B) from localization_eq S φ.toIntAlgHom p g]
  change algebraMap B (Localization.AtPrime p.asIdeal)
    (algebraMap A B (g (projection S φ p) : A)) = _
  simp only [map_intCast]

open CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false in
private theorem pushout (A : Type u) [CommRing A] (S : Profinite.{u}) :
    IsPushout
      (CommRingCat.ofHom ((Int.castRingHom (LocallyConstant S ℤ)).comp
        ULift.ringEquiv.toRingHom) : CommRingCat.of (ULift.{u} ℤ) ⟶ _)
      (CommRingCat.ofHom ((Int.castRingHom A).comp ULift.ringEquiv.toRingHom))
      (CommRingCat.ofHom (LocallyConstant.mapRingHom (Int.castRingHom A)))
      (CommRingCat.ofHom (algebraMap A (LocallyConstant S A))) := by
  apply IsPushout.of_isColimit
    (c := PushoutCocone.mk _ _ (by ext z s; rfl))
  apply PushoutCocone.isColimitAux'
  intro c
  let : Algebra A c.pt := c.inr.hom.toAlgebra
  let d := fromIntegers (A := A) S c.inl.hom
  refine ⟨CommRingCat.ofHom d.toRingHom, ?_, ?_, ?_⟩
  · apply CommRingCat.hom_ext
    exact to_from (A := A) S c.inl.hom
  · ext r
    exact d.commutes r
  · intro m hl hr
    let ψ : LocallyConstant S A →ₐ[A] c.pt :=
      { m.hom with commutes' := fun r ↦ congrArg (fun f ↦ f.hom r) hr }
    have ht : toIntegers S ψ = c.inl.hom := congrArg CommRingCat.Hom.hom hl
    have heq : ψ = d := by
      rw [← from_to S ψ, ht]
    exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom heq)

open AlgebraicGeometry
private theorem pullback (A : Type u) [CommRing A] (S : Profinite.{u}) :
    IsPullback (Spec.map (CommRingCat.ofHom
      (LocallyConstant.mapRingHom (Int.castRingHom A))))
      (Spec.map (CommRingCat.ofHom (algebraMap A (LocallyConstant S A))))
      (toSpecZ (profiniteToScheme.obj S)) (toSpecZ (Spec (.of A))) := by
  have h := isPullback_SpecMap_of_isPushout _ _ _ _ (pushout A S)
  convert h using 1 <;> exact specULiftZIsTerminal.hom_ext _ _
end TestLC

open TopologicalSpace

open TopologicalSpace
private theorem separated (R : Type u) [CommRing R] [Ring.AbsolutelyFlat R] :
    TotallySeparatedSpace (PrimeSpectrum R) := by
  have hc (r : R) : IsClopen (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
    obtain ⟨s, hs⟩ := Ring.AbsolutelyFlat.exists_eq_mul_self_mul r
    have he : r * s * (1 - r * s) = 0 := by
      calc r * s * (1 - r * s) = r * s - r * r * s * s := by ring
           _ = 0 := sub_eq_zero.mpr (congrArg (fun t ↦ t * s) hs)
    have heq : PrimeSpectrum.basicOpen (r * s) = PrimeSpectrum.basicOpen r := by
      apply le_antisymm
      · exact PrimeSpectrum.basicOpen_mul_le_left _ _
      · conv_lhs => rw [hs]
        simp only [PrimeSpectrum.basicOpen_mul, inf_idem]
        exact le_rfl
    rw [← heq]
    exact PrimeSpectrum.isClopen_basicOpen_of_mul_add _ _ he (by ring)
  apply totallySeparatedSpace_of_t0_of_basis_clopen
  apply PrimeSpectrum.isTopologicalBasis_basic_opens.of_isOpen_of_subset
  · exact fun _ h ↦ h.isOpen
  · rintro _ ⟨r, rfl⟩
    exact hc r

namespace AlgebraicGeometry.ProEtale
end AlgebraicGeometry.ProEtale
