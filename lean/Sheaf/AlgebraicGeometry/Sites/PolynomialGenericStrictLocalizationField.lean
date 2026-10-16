/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.Sites.SupportDimension
public import WeilConjectures.ZetaSeries
public import Mathlib.FieldTheory.IsSepClosed
import Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModel
import Sheaf.AlgebraicGeometry.FiniteTypeResidueTrdeg
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import WeilConjectures.Mathlib.AlgebraicGeometry.ResidueField
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import Mathlib.RingTheory.KrullDimension.Zero

/-! # Strict localization at a generic point of polynomial affine space

Source: blueprint `thm-sc-affine-torsion-cd`, exceptional generic degree-two case.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- At a point of polynomial affine m-space whose residue transcendence degree is at
least m, the strict localization is the spectrum of a separably closed field.
Source: blueprint `thm-sc-affine-torsion-cd`, proof step 10 (generic degree two).
(blueprint: lem-sc-polynomial-generic-strict-localization-field)

Proof: finite type makes the residue transcendence degree a finite natural number a.
The polynomial ring has dimension m and is smooth and integral over K. Apply the smooth
strict-local field model, with the canonical scalar structures induced by the structural
maps. Its strict-local ring is a regular local domain of dimension m-a. The hypothesis
m<=a makes this zero. A reduced zero-dimensional local ring is a field, so its residue
map is bijective. The residue field is separably closed, and the resulting ring
isomorphism gives the claimed scheme isomorphism. This also covers m=0. -/
theorem polynomial_generic_strictLocalization_field
    (K : Type u) [Field K] [IsAlgClosed K] (m : ℕ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of (MvPolynomial (Fin m) K)))
    (hs : (m : Cardinal.{u}) ≤ residueFieldTrdeg
      (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin m) K))))
      (s (IsLocalRing.closedPoint Ω))) :
    ∃ (L : Type u) (_ : Field L) (_ : IsSepClosed L),
      Nonempty (strictHenselizationScheme s ≅ Spec (.of L)) := by
  let B := Spec (.of (MvPolynomial (Fin m) K))
  let b : B ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin m) K)))
  let y : B := s (IsLocalRing.closedPoint Ω)
  letI : B.Over (Spec (.of K)) := ⟨b⟩
  have : LocallyOfFiniteType b := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.2 inferInstance
  have : Smooth b := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.2 ⟨inferInstance, inferInstance⟩
  have hd : topologicalKrullDim B = (m : WithBot ℕ∞) := by
    change topologicalKrullDim (PrimeSpectrum (MvPolynomial (Fin m) K)) = _
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  letI : Algebra K (B.residueField y) := (b.residueFieldAlgebraMap y).toAlgebra
  have : LocallyOfFiniteType (B ↘ Spec (.of K)) := by
    change LocallyOfFiniteType b
    infer_instance
  have hfin : Algebra.trdeg K (B.residueField y) < Cardinal.aleph0 :=
    finite_trdeg_residueField y
  obtain ⟨a, ha⟩ := Cardinal.lt_aleph0.mp hfin
  have htr : residueFieldTrdeg b y = (a : Cardinal.{u}) := by
    change @Algebra.trdeg K (B.residueField y) _ _
      (residueFieldHomOfOver b y).toAlgebra = _
    have hscalar : residueFieldHomOfOver b y = b.residueFieldAlgebraMap y := by
      unfold residueFieldHomOfOver Hom.residueFieldAlgebraMap
      congr 1
      rw [Spec.algebraMap_residueFieldIso_inv_assoc, Scheme.residue_residueFieldMap,
        Scheme.Hom.germ_stalkMap_assoc]
      rfl
    rw [hscalar]
    exact ha
  have hma : m ≤ a := by
    exact_mod_cast hs.trans_eq htr
  let χ := (SpecToEquivOfField Ω B s).2
  letI : Algebra (B.residueField y) Ω := χ.hom.toAlgebra
  have hΩ : Spec.map (CommRingCat.ofHom (algebraMap (B.residueField y) Ω)) ≫
      B.fromSpecResidueField y = s := (SpecToEquivOfField Ω B).symm_apply_apply s
  let α := Spec.preimage (strictHenselizationStructuralMap s ≫ b)
  letI : Algebra K (strictHenselizationRing s) := α.hom.toAlgebra
  have hK : Spec.map (CommRingCat.ofHom (algebraMap K (strictHenselizationRing s))) =
      strictHenselizationStructuralMap s ≫ b := Spec.map_preimage _
  have hκ : Spec.map (CommRingCat.ofHom (algebraMap K (B.residueField y))) =
      B.fromSpecResidueField y ≫ b := by
    change Spec.map (CommRingCat.ofHom (b.residueFieldAlgebraMap y)) = _
    unfold Hom.residueFieldAlgebraMap
    rw [CommRingCat.ofHom_hom, Spec.map_comp, Spec.map_comp, Category.assoc,
      Spec.map_residueFieldIso_inv_eq_fromSpecResidueField,
      Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  obtain ⟨_, hl, hdom, hdim, -⟩ := smooth_strict_local_field_model K B b m a hd Ω s y rfl
    hκ hΩ ha hK
  letI := hl
  letI := hdom
  have hdim0 : ringKrullDim (strictHenselizationRing s) = 0 := by
    simpa only [Nat.sub_eq_zero_of_le hma, Nat.cast_zero] using hdim
  have : Ring.KrullDimLE 0 (strictHenselizationRing s) :=
    Ring.krullDimLE_iff.mpr (by simpa only [Nat.cast_zero] using hdim0.le)
  have hf : IsField (strictHenselizationRing s) := Ring.KrullDimLE.isField_of_isReduced
  have hinj : Function.Injective (IsLocalRing.residue (strictHenselizationRing s)) := by
    rw [RingHom.injective_iff_ker_eq_bot, IsLocalRing.ker_residue,
      (IsLocalRing.isField_iff_maximalIdeal_eq).mp hf]
  let e := RingEquiv.ofBijective (IsLocalRing.residue (strictHenselizationRing s))
    ⟨hinj, IsLocalRing.residue_surjective⟩
  exact ⟨IsLocalRing.ResidueField (strictHenselizationRing s), inferInstance,
    inferInstance, ⟨(Scheme.Spec.mapIso e.toCommRingCatIso.op).symm⟩⟩

end AlgebraicGeometry.Scheme
