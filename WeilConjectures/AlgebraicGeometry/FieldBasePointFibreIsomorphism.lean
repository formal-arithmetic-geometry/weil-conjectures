/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# A scheme over a field is its fibre at the unique base point

Source: Stacks Project, Morphisms, Tag 03J5, proof of (1) implies (2), with
Schemes, Tags 01J9, 01JP and 01K0
(blueprint: lem-weil-pbc-field-base-point-fibre-isomorphism).

The field and scheme isomorphisms below have prescribed forward maps. In particular,
the field map is the affine identification followed by the germ and residue maps.
The chosen scheme fibre and every other pullback presentation are both covered.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A scheme over a field is canonically its scheme-theoretic fibre at the unique
point of the base, with the canonical residue morphism and both projections fixed.

Source: Stacks Project, Morphisms, Tag 03J5, proof of (1) implies (2), first paragraph;
Schemes, Tags 01HV, 01I2, 01J9, 01JP and 01K0; Algebra, Tag 00CT
(blueprint: lem-weil-pbc-field-base-point-fibre-isomorphism).

Proof:
1. By lem-weil-pbc-prime-residue-field-algebra, the map from K to the prime residue
   field at zero is injective and makes that residue field a fraction field of K.
   A fraction pi(a)/pi(b) equals pi(a * b⁻¹), proving surjectivity.
2. Use lem-weil-pbc-spec-residue-field-identification to identify the scheme residue
   field with the prime residue field, compatibly with the germ-residue map and its
   spectrum. This gives the field isomorphism e with exactly the displayed forward
   map. Contravariant functoriality of Spec gives the scheme isomorphism j with
   forward map fromSpecResidueField. The global-section identity is precisely
   lem-weil-pbc-spec-map-global-sections applied to e.hom.
3. By def-pc-scheme-fibre and def-pc-fibre-product, the chosen fibre is the pullback.
   Its commutativity gives q = p ≫ h ≫ j.inv. Lift the pair (identity, h ≫ j.inv)
   to r from W to the fibre. Then r ≫ p = identity. The composites of p ≫ r with
   both projections equal the original projections, so pullback uniqueness gives
   p ≫ r = identity. Thus p is an isomorphism.
4. For any other pullback presentation, def-pc-fibre-product gives the unique
   comparison isomorphism c commuting with both projections. Its first projection
   is c.hom ≫ p and is invertible. Commutativity and the formula for the second
   projection follow by composing the chosen-fibre identities with c.hom.

The point ξ may be arbitrary: Spec K has exactly one point, the zero prime.
-/
theorem fieldBasePoint_fibre_isomorphism (K : Type u) [Field K]
    (ξ : Spec (CommRingCat.of K)) :
    ∃ (e : CommRingCat.of K ≅ (Spec (CommRingCat.of K)).residueField ξ)
      (j : Spec ((Spec (CommRingCat.of K)).residueField ξ) ≅ Spec (CommRingCat.of K)),
      e.hom = (ΓSpecIso (CommRingCat.of K)).inv ≫
        (Spec (CommRingCat.of K)).Γevaluation ξ ∧
      j.hom = (Spec (CommRingCat.of K)).fromSpecResidueField ξ ∧
      j.hom = Spec.map e.hom ∧
      (ΓSpecIso (CommRingCat.of K)).inv ≫ j.hom.appTop ≫
        (ΓSpecIso ((Spec (CommRingCat.of K)).residueField ξ)).hom = e.hom ∧
      ∀ (W : Scheme.{u}) (h : W ⟶ Spec (CommRingCat.of K)),
        IsIso (h.fiberι ξ) ∧
        h.fiberι ξ ≫ h = h.fiberToSpecResidueField ξ ≫
          (Spec (CommRingCat.of K)).fromSpecResidueField ξ ∧
        h.fiberToSpecResidueField ξ = h.fiberι ξ ≫ h ≫ j.inv ∧
        ∀ (F : Scheme.{u}) (p : F ⟶ W)
          (q : F ⟶ Spec ((Spec (CommRingCat.of K)).residueField ξ)),
          IsPullback p q h ((Spec (CommRingCat.of K)).fromSpecResidueField ξ) →
          IsIso p ∧
          p ≫ h = q ≫ (Spec (CommRingCat.of K)).fromSpecResidueField ξ ∧
          q = p ≫ h ≫ j.inv ∧
          ∃! c : F ≅ h.fiber ξ,
            c.hom ≫ h.fiberι ξ = p ∧ c.hom ≫ h.fiberToSpecResidueField ξ = q := by
  let e₀ := ξ.asIdeal.algEquivResidueFieldOfField.toRingEquiv.toCommRingCatIso
  let e : CommRingCat.of K ≅ (Spec (CommRingCat.of K)).residueField ξ :=
    e₀ ≪≫ (Spec.residueFieldIso (CommRingCat.of K) ξ).symm
  have he₀ : e₀.hom = CommRingCat.ofHom (algebraMap K ξ.asIdeal.ResidueField) := rfl
  have he : e.hom = (ΓSpecIso (CommRingCat.of K)).inv ≫
      (Spec (CommRingCat.of K)).Γevaluation ξ := by
    change e₀.hom ≫ (Spec.residueFieldIso (CommRingCat.of K) ξ).inv = _
    rw [he₀]
    exact Spec.algebraMap_residueFieldIso_inv _ _
  have hj : Spec.map e.hom = (Spec (CommRingCat.of K)).fromSpecResidueField ξ := by
    change Spec.map (e₀.hom ≫ (Spec.residueFieldIso (CommRingCat.of K) ξ).inv) = _
    rw [Spec.map_comp, he₀]
    exact Spec.map_residueFieldIso_inv_eq_fromSpecResidueField _ _
  let j := asIso (Spec.map e.hom)
  have hj' : j.hom = (Spec (CommRingCat.of K)).fromSpecResidueField ξ := hj
  have : IsIso ((Spec (CommRingCat.of K)).fromSpecResidueField ξ) := hj ▸ inferInstance
  refine ⟨e, j, he, hj', rfl, ?_, ?_⟩
  · change (ΓSpecIso (CommRingCat.of K)).inv ≫ (Spec.map e.hom).appTop ≫ _ = _
    simp only [ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  · intro W h
    have hp : IsIso (h.fiberι ξ) := by
      change IsIso (pullback.fst h ((Spec (CommRingCat.of K)).fromSpecResidueField ξ))
      infer_instance
    refine ⟨hp, h.fiber_fac ξ, ?_, ?_⟩
    · rw [← Category.assoc]
      apply (j.eq_comp_inv).mpr
      rw [hj']
      exact (h.fiber_fac ξ).symm
    · intro F p q H
      refine ⟨H.isIso_fst_of_isIso, H.w, ?_, ?_⟩
      · rw [← Category.assoc]
        apply (j.eq_comp_inv).mpr
        rw [hj']
        exact H.w.symm
      · refine ⟨H.isoPullback, ⟨H.isoPullback_hom_fst, H.isoPullback_hom_snd⟩, ?_⟩
        intro c hc
        apply Iso.ext
        apply pullback.hom_ext
        · exact hc.1.trans H.isoPullback_hom_fst.symm
        · exact hc.2.trans H.isoPullback_hom_snd.symm

end AlgebraicGeometry.Scheme
