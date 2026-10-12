/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups D2 and A3
-/
module

public import Sheaf.AlgebraicGeometry.EtaleResidueTriples

import Sheaf.RingTheory.EtaleResidueTriplesSimpleRootsConstruction
/-!
# EtaleResidueTripleUnitRefinement

Source: Stacks Project, Algebra, Tags 04GN and 04GP.
(blueprint: lem-weil-pbc-etale-triple-unit-refinement).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Algebra, Tags 04GN and 04GP.

Proof: For an element f outside the prime q of a triple, form the principal localization B_f.
The map B → K extends to B_f because the image of f in K is nonzero and hence a unit.
Let q' be the kernel of this extension and extend the resulting injection B_f/q' → K
to its fraction field. This gives the residue-field embedding of the new triple.
The extended map agrees on R, so q' lies over p and the triple is compatible with χ.
Principal localization is etale, and composition with the given etale map is etale.
The localization map is a morphism of triples and takes f to a unit.
(blueprint: lem-weil-pbc-etale-triple-unit-refinement). -/
theorem etaleResidueTriple_unit_refinement
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K)
    (t : EtaleResidueTriples R p K χ) (f : t.B) (hf : f ∉ t.q.asIdeal) :
    ∃ (s : EtaleResidueTriples R p K χ) (a : t ⟶ s),
      IsUnit (((etaleResidueTriplesRingDiagram R p K χ).map a).hom f) := by
  classical
  let β := ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom
  have hfβ : IsUnit (β f) :=
    isUnit_iff_ne_zero.mpr (fun h ↦ hf ((triple_map_eq_zero t f).mp h))
  let L := Localization.Away f
  let γ : L →+* K := IsLocalization.Away.lift f hfβ
  let q : Spec (CommRingCat.of L) := ⟨RingHom.ker γ, RingHom.ker_isPrime _⟩
  have : q.asIdeal.IsPrime := q.isPrime
  have hunit : q.asIdeal.primeCompl ≤ Submonoid.comap γ (IsUnit.submonoid K) :=
    fun x hx ↦ isUnit_iff_ne_zero.mpr (by simpa [q, RingHom.mem_ker] using hx)
  let e : q.asIdeal.ResidueField →+* K :=
    Ideal.ResidueField.lift q.asIdeal γ le_rfl hunit
  let φ : (Spec (CommRingCat.of L)).residueField q ⟶ CommRingCat.of K :=
    (Spec.residueFieldIso (CommRingCat.of L) q).hom ≫ CommRingCat.ofHom e
  have hγ : (ΓSpecIso (CommRingCat.of L)).inv ≫
      (Spec (CommRingCat.of L)).Γevaluation q ≫ φ = CommRingCat.ofHom γ := by
    have he := Spec.algebraMap_residueFieldIso_inv (CommRingCat.of L) q
    change CommRingCat.ofHom (algebraMap L q.asIdeal.ResidueField) ≫
      (Spec.residueFieldIso (CommRingCat.of L) q).inv =
        (ΓSpecIso (CommRingCat.of L)).inv ≫
          (Spec (CommRingCat.of L)).Γevaluation q at he
    rw [← Category.assoc, ← he]
    dsimp only [φ]
    rw [Category.assoc, Iso.inv_hom_id_assoc]
    apply CommRingCat.hom_ext
    ext x
    exact Ideal.ResidueField.lift_algebraMap q.asIdeal γ le_rfl hunit x
  let i : t.B ⟶ CommRingCat.of L := CommRingCat.ofHom (algebraMap t.B L)
  have hi : i ≫ CommRingCat.ofHom γ =
      (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ := by
    apply CommRingCat.hom_ext
    ext x
    change γ (algebraMap t.B L x) = β x
    exact IsLocalization.Away.lift_eq (S := L) f hfβ x
  have hq : Spec.map i q = t.q := by
    apply PrimeSpectrum.ext
    ext x
    change γ (algebraMap t.B L x) = 0 ↔ x ∈ t.q.asIdeal
    rw [IsLocalization.Away.lift_eq (S := L) f hfβ]
    exact triple_map_eq_zero t x
  have : Etale (Spec.map i) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact (RingHom.etale_algebraMap).mpr (Algebra.Etale.of_isLocalizationAway f)
  have : Etale (Spec.map t.α) := t.etale
  let s : EtaleResidueTriples R p K χ :=
    { B := CommRingCat.of L
      α := t.α ≫ i
      etale := by rw [Spec.map_comp]; infer_instance
      q := q
      over := by
        rw [Spec.map_comp]
        change Spec.map t.α (Spec.map i q) = p
        rw [hq, t.over]
      φ := φ
      compatible := by rw [Category.assoc, hγ, hi]; exact t.compatible }
  let a : t ⟶ s := InducedCategory.homMk
    (Under.homMk (Over.homMk i (by
      change i ≫ ((ΓSpecIso (CommRingCat.of L)).inv ≫
        (Spec (CommRingCat.of L)).Γevaluation q ≫ φ) = _
      rw [hγ, hi]
      rfl)) (by rfl))
  refine ⟨s, a, ?_⟩
  change IsUnit (algebraMap t.B L f)
  exact IsLocalization.Away.algebraMap_isUnit f

end AlgebraicGeometry.Scheme
