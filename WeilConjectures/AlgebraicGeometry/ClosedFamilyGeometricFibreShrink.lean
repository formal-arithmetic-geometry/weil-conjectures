/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.GenericGeometricIrreducibilityShrink

/-! # Simultaneous geometric irreducibility on an open

## References

* Stacks Project, Tags 0559 and 055G
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Topology
namespace AlgebraicGeometry

private theorem irreducibleSpace_iff_range {X Y : Scheme.{u}} (j : X ⟶ Y)
    (hj : IsEmbedding j) : IrreducibleSpace X ↔ IsIrreducible (Set.range j) := by
  rw [isIrreducible_iff_irreducibleSpace]
  exact hj.toHomeomorph.irreducibleSpace_iff

private theorem closed_baseChange_irreducible_iff {Z P T B : Scheme.{u}}
    (j : Z ⟶ P) [IsClosedImmersion j] (p : P ⟶ T) (g : B ⟶ T) :
    IrreducibleSpace ↥(pullback (j ≫ p) g) ↔
      IsIrreducible ((pullback.fst p g) ⁻¹' Set.range j) := by
  rw [← (pullbackRightPullbackFstIso p g j).hom.homeomorph.irreducibleSpace_iff]
  rw [irreducibleSpace_iff_range _ (pullback.snd j (pullback.fst p g)).isEmbedding]
  rw [Scheme.Pullback.range_snd]

set_option backward.isDefEq.respectTransparency false in
private theorem closed_geometric_fibre_irreducible_iff {Z P T : Scheme.{u}}
    (j : Z ⟶ P) [IsClosedImmersion j] (p : P ⟶ T) (t : T) :
    GeometricallyIrreducible ((j ≫ p).fiberToSpecResidueField t) ↔
      ∀ (E : Type u) (_ : Field E)
        (z : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of (T.residueField t))),
        IsIrreducible ((pullback.fst (p.fiberToSpecResidueField t) z ≫
          p.fiberι t) ⁻¹' Set.range j) := by
  rw [GeometricallyIrreducible.eq_geometrically,
    geometrically_iff_of_isClosedUnderIsomorphisms]
  dsimp [Scheme.Hom.fiberToSpecResidueField, Scheme.Hom.fiberι, Scheme.Hom.fiber]
  constructor
  · intro h E hE z
    have hZ := h E z
    let eZ := pullbackLeftPullbackSndIso (j ≫ p) (T.fromSpecResidueField t) z
    rw [eZ.hom.homeomorph.irreducibleSpace_iff] at hZ
    have hP := (closed_baseChange_irreducible_iff j p (z ≫ T.fromSpecResidueField t)).mp hZ
    let eP := pullbackLeftPullbackSndIso p (T.fromSpecResidueField t) z
    have h := hP.preimage eP.hom.isOpenEmbedding (by
      simpa [Set.range_eq_univ.mpr eP.hom.surjective] using hP.nonempty)
    change IsIrreducible ((eP.hom ≫ pullback.fst p
      (z ≫ T.fromSpecResidueField t)) ⁻¹' Set.range j) at h
    rw [pullbackLeftPullbackSndIso_hom_fst] at h
    exact h
  · intro h E hE z
    let eP := pullbackLeftPullbackSndIso p (T.fromSpecResidueField t) z
    have hP := (h E hE z).image eP.hom eP.hom.continuous.continuousOn
    have hpre : (pullback.fst (pullback.snd p (T.fromSpecResidueField t)) z ≫
        pullback.fst p (T.fromSpecResidueField t)) ⁻¹' Set.range j = eP.hom ⁻¹'
          ((pullback.fst p (z ≫ T.fromSpecResidueField t)) ⁻¹' Set.range j) := by
      change _ = (eP.hom ≫ pullback.fst p (z ≫ T.fromSpecResidueField t)) ⁻¹' _
      rw [pullbackLeftPullbackSndIso_hom_fst]
      rfl
    change IsIrreducible (eP.hom '' ((pullback.fst
      (pullback.snd p (T.fromSpecResidueField t)) z ≫
        pullback.fst p (T.fromSpecResidueField t)) ⁻¹' Set.range j)) at hP
    rw [hpre, Set.image_preimage_eq _ eP.hom.surjective] at hP
    have hZ := (closed_baseChange_irreducible_iff j p (z ≫ T.fromSpecResidueField t)).mpr hP
    let eZ := pullbackLeftPullbackSndIso (j ≫ p) (T.fromSpecResidueField t) z
    exact eZ.hom.homeomorph.irreducibleSpace_iff.mpr hZ

/-- A finite family of generically geometrically irreducible closed subsets has
geometrically irreducible fibres on a common open (Stacks, Tags 0559 and 055G). -/
theorem exists_open_closed_family_geometric_fibre_shrink {P T : Scheme.{u}}
    (p : P ⟶ T) [LocallyOfFiniteType p] [QuasiCompact p]
    (η : T) (hη : IsGenericPoint η Set.univ) {I : Type u} [Finite I]
    (C : I → Set P) (hclosed : ∀ i, IsClosed (C i))
    (hgeom : ∀ i, ∀ (E : Type u) (_ : Field E)
      (z : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of (T.residueField η))),
      IsIrreducible ((pullback.fst (p.fiberToSpecResidueField η) z ≫
        p.fiberι η) ⁻¹' C i)) :
    ∃ U : T.Opens, η ∈ U ∧ ∀ i t, t ∈ U →
      ∀ (E : Type u) (_ : Field E)
        (z : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of (T.residueField t))),
        IsIrreducible ((pullback.fst (p.fiberToSpecResidueField t) z ≫
          p.fiberι t) ⁻¹' C i) := by
  classical
  let J (i : I) := Scheme.IdealSheafData.vanishingIdeal
    (⟨C i, hclosed i⟩ : TopologicalSpace.Closeds P)
  have hrange (i : I) : Set.range (J i).subschemeι = C i := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    rfl
  have hgeneric (i : I) :
      GeometricallyIrreducible (((J i).subschemeι ≫ p).fiberToSpecResidueField η) := by
    apply (closed_geometric_fibre_irreducible_iff (J i).subschemeι p η).mpr
    simpa only [hrange] using hgeom i
  have hshrink (i : I) := exists_open_generic_geometric_irreducibility_shrink
    ((J i).subschemeι ≫ p) η hη (hgeneric i)
  choose U hηU hU using hshrink
  refine ⟨⨅ i, U i, ?_, ?_⟩
  · change η ∈ (↑(⨅ i, U i) : Set T)
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr hηU
  · intro i t ht E hE z
    have hi : t ∈ U i := (iInf_le U i) ht
    have h := (closed_geometric_fibre_irreducible_iff (J i).subschemeι p t).mp
      (hU i t hi) E hE z
    simpa only [hrange] using h

end AlgebraicGeometry
