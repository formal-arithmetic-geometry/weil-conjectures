/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModelCore
import Sheaf.RingTheory.HenselianSeparablyGeneratedResidueSection
import Sheaf.Paper.StrictHenselizationFunctoriality
import Mathlib.FieldTheory.SeparablyGenerated
import WeilConjectures.PointCount

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
  let k := Y.residueField y
  let R := strictHenselizationRing s
  let : Algebra K Ω := ((algebraMap k Ω).comp (algebraMap K k)).toAlgebra
  let : IsScalarTower K k Ω := IsScalarTower.of_algebraMap_eq' rfl
  let E := separableClosure k Ω
  let : Algebra K E := inferInstance
  let : IsScalarTower K k E := inferInstance
  obtain ⟨_, hl, hdom, _, e, he, _⟩ :=
    smooth_strict_local_field_model_core K Y f d a hd Ω s y hy hκ hΩ ha hK
  have hstrict : IsStrictlyHenselianLocalRing R := by
    let : Algebra (Y.residueField (s (IsLocalRing.closedPoint Ω))) Ω :=
      (Scheme.descResidueField (Scheme.stalkClosedPointTo s)).hom.toAlgebra
    exact (AlgebraicGeometry.strictHenselizationResidue s rfl).choose_spec.1
  let := hstrict
  let ρ₀ : R →+* E := e.toRingHom.comp (IsLocalRing.residue R)
  have hρK : ρ₀.comp (algebraMap K R) = algebraMap K E := by
    have hh : CommRingCat.ofHom
        ((E.subtype.comp ρ₀).comp (algebraMap K R)) =
        CommRingCat.ofHom (algebraMap K Ω) := by
      apply Spec.map_injective
      change Spec.map (CommRingCat.ofHom (algebraMap K R) ≫
        CommRingCat.ofHom (E.subtype.comp ρ₀)) = _
      rw [Spec.map_comp, hK, ← Category.assoc, he]
      change s ≫ f = Spec.map
        (CommRingCat.ofHom (algebraMap K k) ≫ CommRingCat.ofHom (algebraMap k Ω))
      rw [Spec.map_comp, hκ, ← Category.assoc, hΩ]
    apply RingHom.ext
    intro c
    apply E.subtype.injective
    exact congrArg (fun g ↦ g.hom c) hh
  let ρ : R →ₐ[K] E := { ρ₀ with commutes' := DFunLike.congr_fun hρK }
  have hsurj : Function.Surjective ρ :=
    e.surjective.comp IsLocalRing.residue_surjective
  have hker : RingHom.ker ρ.toRingHom = IsLocalRing.maximalIdeal R := by
    ext x
    change e (IsLocalRing.residue R x) = 0 ↔ _
    rw [map_eq_zero, IsLocalRing.residue_eq_zero_iff]
  have hfinite : Algebra.EssFiniteType K k := by
    have heq : algebraMap K k = f.residueFieldAlgebraMap y := by
      have hh : CommRingCat.ofHom (algebraMap K k) =
          CommRingCat.ofHom (f.residueFieldAlgebraMap y) := by
        apply Spec.map_injective
        exact hκ.trans (f.specMap_residueFieldAlgebraMap y).symm
      exact congrArg CommRingCat.Hom.hom hh
    rw [← RingHom.essFiniteType_algebraMap, heq]
    have h₁ : (algebraMap K (f y).asIdeal.ResidueField).EssFiniteType := by
      rw [RingHom.essFiniteType_algebraMap]
      infer_instance
    have h₂ : (Spec.residueFieldIso (.of K) (f y)).inv.hom.EssFiniteType :=
      (RingHom.FiniteType.of_surjective _
        (Spec.residueFieldIso (.of K) (f y)).symm.commRingCatIsoToRingEquiv.surjective
        ).essFiniteType
    exact (h₁.comp h₂).comp (LocallyOfFiniteType.stalkMap f y).residueFieldMap
  let := hfinite
  obtain ⟨t, ht, hsep⟩ :=
    exists_isTranscendenceBasis_and_isSeparable_of_perfectField K k
  let v : t → E := fun x ↦ algebraMap k E x
  have hv : AlgebraicIndependent K v :=
    ht.1.map (f := IsScalarTower.toAlgHom K k E) (algebraMap k E).injective.injOn
  let L₀ := IntermediateField.adjoin K (t : Set k)
  let L := IntermediateField.adjoin K (Set.range v)
  let : Algebra.IsSeparable L₀ k := hsep
  let : Algebra.IsSeparable L₀ E := Algebra.IsSeparable.trans L₀ k E
  let φ : k →ₐ[K] E := IsScalarTower.toAlgHom K k E
  have hL : L₀.map φ = L := by
    rw [IntermediateField.adjoin_map]
    congr 1
    exact Set.image_eq_range _ _
  let eL : L₀ ≃ₐ[K] L :=
    (IntermediateField.equivMap L₀ φ).trans (IntermediateField.equivOfEq hL)
  have hbase : (algebraMap L E).comp eL.toRingEquiv.toRingHom =
      (RingEquiv.refl E).toRingHom.comp (algebraMap L₀ E) := by
    apply RingHom.ext
    intro x
    change (eL x : E) = algebraMap L₀ E x
    change φ x = algebraMap L₀ E x
    rfl
  let : Algebra.IsSeparable L E :=
    Algebra.IsSeparable.of_equiv_equiv eL.toRingEquiv (RingEquiv.refl E) hbase
  obtain ⟨j, hj⟩ := Algebra.exists_section_of_separating_family K E R ρ hsurj hker t v hv
  let : IsSepClosed E := IsSepClosure.sep_closed k
  refine ⟨E, inferInstance, inferInstance, j, inferInstance, ?_, ?_⟩
  · have hh : (IsLocalRing.residue R).comp j.toRingHom = e.symm.toRingHom := by
      ext x
      apply e.injective
      exact (DFunLike.congr_fun hj x).trans (e.apply_symm_apply x).symm
    rw [hh]
    exact e.symm.bijective
  · have htower := trdeg_add_eq (R := K) (S := k) (A := E)
    rw [trdeg_eq_zero (R := k), add_zero, ha] at htower
    exact htower.symm

end Scheme
end AlgebraicGeometry
