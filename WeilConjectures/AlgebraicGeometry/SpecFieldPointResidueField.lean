/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField

/-! # Morphisms from a field spectrum and residue fields

Source: Stacks Project, Schemes, discussion before Lemma 01J9, and Algebra,
Local rings and Proposition 00CT (blueprint: lem-weil-pbc-spec-field-point-residue-field).

## Main statements

* `spec_field_point_residue_field`: the affine residue field and its canonical ring map.
* `spec_field_point_residue_field_affine_open`: the affine-open factorization.
* `spec_field_point_residue_field_map`: the kernel point and unique residue-field extension.
* `spec_field_point_residue_field_generic`: the generic-point fraction-field case.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Stacks, Schemes, discussion before 01J9; Algebra, 00E2 and 00CT
(blueprint: lem-weil-pbc-spec-field-point-residue-field), clause (3).

Proof: Spec of a field has the unique prime zero. The point map is prime comap,
so its image ideal is the kernel (`def-weil-affine-spectrum`). Use
`lem-weil-pbc-morphism-from-spec-field` to factor the morphism through the image's
canonical residue-field point. Under `lem-weil-pbc-spec-residue-field-identification`,
full faithfulness of Spec says that the induced field map extends the given ring map.
By clause (1) this is extension of the injection from the prime quotient to its fraction
field. Uniqueness is `lem-weil-pbc-prime-residue-field-algebra`, clause (c). -/
theorem spec_field_point_residue_field_map
    (R : Type u) [CommRing R] (K : Type u) [Field K] (ψ : R →+* K) :
    ∃ (q : PrimeSpectrum R)
      (hq : Spec.map (CommRingCat.ofHom ψ) (IsLocalRing.closedPoint K) = q)
      (l : CommRingCat.of q.asIdeal.ResidueField ⟶ CommRingCat.of K),
      q.asIdeal = RingHom.ker ψ ∧
      l = (Scheme.Spec.residueFieldIso (.of R) q).inv ≫
        ((Spec (.of R)).residueFieldCongr hq).inv ≫
        (Spec (.of R)).descResidueField
          (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom ψ))) ∧
      l.hom.comp (algebraMap R q.asIdeal.ResidueField) = ψ ∧
      ∀ (l' : q.asIdeal.ResidueField →+* K),
        l'.comp (algebraMap R q.asIdeal.ResidueField) = ψ → l' = l.hom := by
  let q := Spec.map (CommRingCat.ofHom ψ) (IsLocalRing.closedPoint K)
  let l := (Scheme.Spec.residueFieldIso (.of R) q).inv ≫
    (Spec (.of R)).descResidueField
      (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom ψ)))
  have hl : l.hom.comp (algebraMap R q.asIdeal.ResidueField) = ψ := by
    have h := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField
      K (Spec (.of R)) (Spec.map (CommRingCat.ofHom ψ))
    rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField] at h
    rw [← Spec.map_comp_assoc, ← Spec.map_comp] at h
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  refine ⟨q, rfl, l, ?_, ?_, hl, ?_⟩
  · change Ideal.comap ψ (IsLocalRing.maximalIdeal K) = RingHom.ker ψ
    rw [IsLocalRing.maximalIdeal_eq_bot]
    rfl
  · simp only [Scheme.residueFieldCongr_refl, Iso.refl_inv]
    exact (Category.id_comp _).symm
  · intro l' hl'
    exact Ideal.ResidueField.ringHom_ext (hl'.trans hl.symm)

end AlgebraicGeometry
