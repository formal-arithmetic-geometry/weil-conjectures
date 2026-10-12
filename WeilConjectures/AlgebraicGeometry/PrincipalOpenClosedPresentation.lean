/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed

/-!
# Principal opens of quotients of normal domains with separably closed fraction field

Let `R` be a normal domain whose fraction field is separably closed. For an ideal `I` of `R` and
`h : R ⧸ I`, the principal open `D(h) ⊆ Spec (R ⧸ I)` is a closed subscheme of `Spec S` for a
normal domain `S` with separably closed fraction field: take `S = R_f` for a lift `f` of `h`.
This is a step in Gabber's proof of the affine analogue of proper base change.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Let `R` be a normal domain with separably closed fraction field, `I` an ideal of `R` and
`h ∈ R ⧸ I`. Then there are a normal domain `S` with separably closed fraction field and a closed
immersion of the principal open `D(h)` of `Spec (R ⧸ I)` into `Spec S`.

(blueprint: `lem-weil-pbc-gabber-principal-open-closed-presentation`) -/
theorem gabber_principal_open_closed_presentation {R : Type u} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [IsSepClosed (FractionRing R)] (I : Ideal R) (h : R ⧸ I) :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsDomain S) (_ : IsIntegrallyClosed S)
      (_ : IsSepClosed (FractionRing S))
      (ι : Scheme.Opens.toScheme (X := Spec (.of (R ⧸ I))) (PrimeSpectrum.basicOpen h) ⟶
        Spec (.of S)),
      IsClosedImmersion ι := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective h
  by_cases hf : f = 0
  · subst hf
    have : IsEmpty (Scheme.Opens.toScheme (X := Spec (.of (R ⧸ I)))
        (PrimeSpectrum.basicOpen (Ideal.Quotient.mk I 0))) := by
      refine ⟨fun x ↦ ?_⟩
      have := x.2
      simp only [map_zero, PrimeSpectrum.basicOpen_zero] at this
      exact this
    refine ⟨R, inferInstance, inferInstance, inferInstance, inferInstance,
      isInitialOfIsEmpty.to _, ?_⟩
    infer_instance
  let S := Localization.Away f
  have hle : Submonoid.powers f ≤ nonZeroDivisors R :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hf
  have : IsDomain S := IsLocalization.isDomain_localization hle
  have : IsIntegrallyClosed S := isIntegrallyClosed_of_isLocalization _ (Submonoid.powers f) hle
  let := IsLocalization.localizationAlgebraOfSubmonoidLe S (FractionRing R) _ _ hle
  have := IsLocalization.localization_isScalarTower_of_submonoid_le S (FractionRing R) _ _ hle
  have : IsFractionRing S (FractionRing R) :=
    IsFractionRing.isFractionRing_of_isLocalization (Submonoid.powers f) S _ hle
  have : IsSepClosed (FractionRing S) :=
    IsSepClosed.of_ringEquiv (FractionRing.algEquiv S (FractionRing R)).symm.toRingEquiv
  have hsurj : Function.Surjective (Localization.awayMap (Ideal.Quotient.mk I) f) := by
    rw [Localization.awayMap_surjective_iff]
    intro a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨b, 0, by simp⟩
  have := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (Localization.awayMap (Ideal.Quotient.mk I) f)) hsurj
  exact ⟨S, inferInstance, inferInstance, inferInstance, inferInstance,
    (basicOpenIsoSpecAway (R := .of (R ⧸ I)) (Ideal.Quotient.mk I f)).hom ≫
      Spec.map (CommRingCat.ofHom (Localization.awayMap (Ideal.Quotient.mk I) f)), inferInstance⟩

end AlgebraicGeometry
