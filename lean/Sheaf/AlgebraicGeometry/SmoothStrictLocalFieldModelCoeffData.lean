/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModelCore
import Sheaf.RingTheory.HenselianSeparablyGeneratedResidueSection
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import WeilConjectures.PointCount
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Coefficient-field construction interface

Source: blueprint thm-sc-affine-torsion-cd, local calculation in dimension d;
Stacks Tags 04HX, 04GP, 04GG and 06RR.

This is the coefficient-field construction part of the smooth strict-local-field
argument.  The construction is isolated here so that the transcendence-degree
calculation can be checked independently.
(blueprint: new-lem-sc-smooth-strict-local-field-model-coeff-data)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Construct a separably closed coefficient field lifting the residue field.

Source: blueprint, sec-smooth-purity/sk-prop-sf-cbc/thm-sc-affine-torsion-cd,
local calculation in dimension d; Stacks Tags 04HX, 04GP, 04GG and 06RR.
(blueprint: new-lem-sc-smooth-strict-local-field-model-coeff-data)

Proof: use the smooth strict-local-field core to identify the residue field with
the separable closure of the point residue field.  Choose a separating
transcendence basis of the finitely generated residue extension and lift its
elements through the residue map.  Nonzero polynomial evaluations are units,
so these lifts embed the rational function field.  The remaining residue extension is
separable algebraic, hence ind-etale. Apply the proved henselian-colimit section
theorem, which assembles the unique lifts at finite etale stages. Reduction is
inverse to this section after the residue-field comparison, and algebraicity
over the point residue field computes the displayed transcendence degree.
-/
theorem exists_smooth_strict_local_field_coeff_data
    (K : Type u) [Field K] [IsAlgClosed K] (Y : Scheme.{u}) [IsIntegral Y]
    (f : Y ⟶ Spec (.of K)) [Smooth f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d a : ℕ) (hd : topologicalKrullDim Y = (d : WithBot ℕ∞))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (y : Y) (hy : s (IsLocalRing.closedPoint Ω) = y)
    [Algebra K (Y.residueField y)]
    (hκ : Spec.map (CommRingCat.ofHom (algebraMap K (Y.residueField y))) =
      Y.fromSpecResidueField y ≫ f)
    [Algebra (Y.residueField y) Ω]
    (hΩ : Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) Ω)) ≫
      Y.fromSpecResidueField y = s)
    (ha : Algebra.trdeg K (Y.residueField y) = (a : Cardinal))
    [Algebra K (strictHenselizationRing s)]
    (hK : Spec.map (CommRingCat.ofHom (algebraMap K (strictHenselizationRing s))) =
      strictHenselizationStructuralMap s ≫ f)
    [IsLocalRing (strictHenselizationRing s)] :
    ∃ (F : Type u) (_ : Field F) (_ : Algebra K F),
      ∃ j : F →ₐ[K] strictHenselizationRing s,
        IsSepClosed F ∧
        Function.Bijective ((IsLocalRing.residue (strictHenselizationRing s)).comp
          j.toRingHom) ∧
        Algebra.trdeg K F = (a : Cardinal) := by
  classical
  let R := strictHenselizationRing s
  let k := Y.residueField y
  let l := separableClosure k Ω
  obtain ⟨_, hl, hdom, _, e, he, i, hi, halg⟩ :=
    smooth_strict_local_field_model_core K Y f d a hd Ω s y hy hκ hΩ ha hK
  let : Algebra K l := ((algebraMap k l).comp (algebraMap K k)).toAlgebra
  let : IsScalarTower K k l := IsScalarTower.of_algebraMap_eq' rfl
  let ρ : R →+* l := e.toRingHom.comp (IsLocalRing.residue R)
  have hρK : ρ.comp (algebraMap K R) = algebraMap K l := by
    apply RingHom.ext
    intro c
    apply l.subtype.injective
    have hm : CommRingCat.ofHom (l.subtype.comp (ρ.comp (algebraMap K R))) =
        CommRingCat.ofHom (l.subtype.comp (algebraMap K l)) := by
      apply Spec.map_injective
      change Spec.map (CommRingCat.ofHom (algebraMap K R) ≫
        CommRingCat.ofHom (l.subtype.comp ρ)) = _
      rw [Spec.map_comp, hK, ← Category.assoc, he]
      change s ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K k) ≫
        CommRingCat.ofHom (algebraMap k Ω))
      rw [Spec.map_comp, hκ, ← Category.assoc, hΩ]
    exact congrArg (fun g ↦ g.hom c) hm
  let ρK : R →ₐ[K] l := { ρ with commutes' c := DFunLike.congr_fun hρK c }
  have hsurj : Function.Surjective ρK :=
    e.surjective.comp IsLocalRing.residue_surjective
  have hker : RingHom.ker ρK.toRingHom = IsLocalRing.maximalIdeal R :=
    IsLocalRing.ker_eq_maximalIdeal ρK.toRingHom hsurj
  have hk : algebraMap K k = f.residueFieldAlgebraMap y := by
    exact congrArg CommRingCat.Hom.hom
      (Spec.map_injective (hκ.trans (f.specMap_residueFieldAlgebraMap y).symm))
  have hft : (f.residueFieldAlgebraMap y).EssFiniteType := by
    have hb : (algebraMap K (f y).asIdeal.ResidueField).EssFiniteType :=
      RingHom.essFiniteType_algebraMap.mpr inferInstance
    have heq : (Spec.residueFieldIso (.of K) (f y)).inv.hom.EssFiniteType :=
      (RingHom.FiniteType.of_surjective _
        (Spec.residueFieldIso (.of K) (f y)).symm.commRingCatIsoToRingEquiv.surjective
        ).essFiniteType
    have hr : (f.residueFieldMap y).hom.EssFiniteType :=
      (LocallyOfFiniteType.stalkMap f y).residueFieldMap
    exact hb.comp (heq.comp hr)
  have : Algebra.EssFiniteType K k := by
    rw [← RingHom.essFiniteType_algebraMap, hk]
    exact hft
  obtain ⟨t, ht, hsep⟩ :=
    exists_isTranscendenceBasis_and_isSeparable_of_perfectField K k
  let := hsep
  let L := IntermediateField.adjoin K (t : Set k)
  let g : k →ₐ[K] l := IsScalarTower.toAlgHom K k l
  let v : t → l := fun x ↦ g x
  have hv : AlgebraicIndependent K v := ht.1.map' (f := g) g.injective
  let M := L.map g
  have hM : M = IntermediateField.adjoin K (Set.range v) := by
    change (IntermediateField.adjoin K (t : Set k)).map g = _
    rw [IntermediateField.adjoin_map]
    exact congrArg (IntermediateField.adjoin K) (Set.image_eq_range g (t : Set k))
  let eL : L ≃ₐ[K] M := L.equivMap g
  have : Algebra.IsSeparable L l := Algebra.IsSeparable.trans L k l
  have hsepM : Algebra.IsSeparable M l :=
    Algebra.IsSeparable.of_equiv_equiv eL.toRingEquiv (RingEquiv.refl l) (by
      apply RingHom.ext
      intro x
      exact IntermediateField.coe_equivMap_apply L g x)
  rw [hM] at hsepM
  let := hsepM
  obtain ⟨j, hj⟩ := Algebra.exists_section_of_separating_family K l R ρK hsurj hker t v hv
  have hred : (IsLocalRing.residue R).comp j.toRingHom = e.symm.toRingHom := by
    ext x
    apply e.injective
    have hx := DFunLike.congr_fun hj x
    change e (IsLocalRing.residue R (j x)) = x at hx
    change e (IsLocalRing.residue R (j x)) = e (e.symm x)
    rw [e.apply_symm_apply]
    exact hx
  have htr : Algebra.trdeg K l = (a : Cardinal) := by
    have htower := trdeg_add_eq (R := K) (S := k) (A := l)
    rw [trdeg_eq_zero (R := k), add_zero, ha] at htower
    exact htower.symm
  refine ⟨l, inferInstance, inferInstance, j, ?_, ?_, htr⟩
  · exact IsSepClosure.sep_closed k
  · rw [hred]
    exact e.symm.bijective

end Scheme
end AlgebraicGeometry
