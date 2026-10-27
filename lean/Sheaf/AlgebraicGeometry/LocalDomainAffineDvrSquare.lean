module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.LocalSubring
public import Mathlib.RingTheory.RingHom.FiniteType

import Sheaf.RingTheory.DiscreteValuationRing.FinitelyGeneratedExtension
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.RingHom.EssFiniteType
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# An affine DVR square from a local domain

Source: Stacks Project, Limits, Tag 0CM2, proof of
`limits-lemma-reach-point-closure-Noetherian`, and Algebra, Tag 00PH,
`algebra-lemma-exists-dvr` (blueprint: lem-sfb-local-domain-affine-dvr-square).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A compatible nonfield Noetherian local subring of a residue field extends to a
DVR subring with that residue field as fraction field and with the prescribed centre.
The maps in the affine square are the spectra of the residue map and the inclusions.

Source: Stacks Project, Limits, Tag 0CM2, proof, final displayed diagram and its centre;
Algebra, Tag 00PH (blueprint: lem-sfb-local-domain-affine-dvr-square).

Proof:
1. Let K be the fraction subfield of R in κ(r). Finite type of φ implies that κ(r) is
   finitely generated over the image of κ(φ⁻¹(r)), by
   [lem-weil-pbc-finite-type-residue-field-extension-finitely-generated]. The hypothesis
   identifying that image with the quotients from R makes κ(r)/K finitely generated.
2. Apply [lem-sfb-local-domain-fg-field-dvr] to R, K and κ(r). The Noetherian local
   domain R is not a field. Obtain a DVR A inside κ(r) containing R, with fraction field
   κ(r), whose maximal ideal contracts to the maximal ideal of R.
3. Write i : R → A and ℓ : A → κ(r) for the inclusions. Compatibility of α gives
   ℓ ∘ i ∘ α = β ∘ φ. Contravariant functoriality of Spec
   [def-weil-affine-spectrum] gives Spec(β) ≫ Spec(φ) = Spec(ℓ) ≫ Spec(i ∘ α).
4. The image of the maximal-ideal point under Spec(i ∘ α) is the inverse image of
   that maximal ideal [lem-weil-pbc-spec-map-stalk-localization]. Contracting first
   along i gives the maximal ideal of R, so this point is α⁻¹(m_R), as required.
-/
theorem exists_affine_dvr_square_of_local_domain
    {B C : Type u} [CommRing B] [CommRing C]
    (φ : B →+* C) (hφ : φ.FiniteType) (r : Ideal C) [r.IsPrime]
    (R : LocalSubring r.ResidueField) [IsNoetherianRing R.toSubring]
    (hR : ¬ IsField R.toSubring) (α : B →+* R.toSubring)
    (hα : R.toSubring.subtype.comp α = (algebraMap C r.ResidueField).comp φ)
    (hFrac : {x : r.ResidueField | ∃ a b : R.toSubring,
        b ≠ 0 ∧ x = (a : r.ResidueField) / (b : r.ResidueField)} =
      Set.range (Ideal.ResidueField.map (r.comap φ) r φ rfl)) :
    ∃ (A : LocalSubring r.ResidueField) (hRA : R.toSubring ≤ A.toSubring),
      IsDiscreteValuationRing A.toSubring ∧ IsFractionRing A.toSubring r.ResidueField ∧
      Ideal.comap (Subring.inclusion hRA) (IsLocalRing.maximalIdeal A.toSubring) =
        IsLocalRing.maximalIdeal R.toSubring ∧
      Spec.map (CommRingCat.ofHom (algebraMap C r.ResidueField)) ≫
          Spec.map (CommRingCat.ofHom φ) =
        Spec.map (CommRingCat.ofHom A.toSubring.subtype) ≫
          Spec.map (CommRingCat.ofHom ((Subring.inclusion hRA).comp α)) ∧
      Spec.map (CommRingCat.ofHom ((Subring.inclusion hRA).comp α))
          (IsLocalRing.closedPoint A.toSubring) =
        PrimeSpectrum.comap α (IsLocalRing.closedPoint R.toSubring) := by
  sorry

end AlgebraicGeometry
