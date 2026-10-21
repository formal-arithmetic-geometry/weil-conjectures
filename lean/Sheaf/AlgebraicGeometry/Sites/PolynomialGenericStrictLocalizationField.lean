/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import WeilConjectures.AlgebraicGeometry.Sites.SupportDimension
public import WeilConjectures.ZetaSeries
public import Mathlib.FieldTheory.IsSepClosed
import Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModelCore
import Sheaf.AlgebraicGeometry.FiniteTypeResidueTrdeg
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import WeilConjectures.PointCount
import Mathlib.RingTheory.KrullDimension.Zero
import all Sheaf.AlgebraicGeometry.Sites.AffineLineInfinityStrictLocalModel

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
  let B : Scheme := Spec (.of (MvPolynomial (Fin m) K))
  let b : B ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin m) K)))
  let y : B := s (IsLocalRing.closedPoint Ω)
  let q := SpecToEquivOfField Ω B
  let r : B.residueField y ⟶ CommRingCat.of Ω := (q s).2
  have hy : s (IsLocalRing.closedPoint Ω) = y := rfl
  letI : Algebra K (B.residueField y) := (b.residueFieldAlgebraMap y).toAlgebra
  letI : Algebra (B.residueField y) Ω := r.hom.toAlgebra
  have hΩ : Spec.map (CommRingCat.ofHom (algebraMap (B.residueField y) Ω)) ≫
      B.fromSpecResidueField y = s := by
    change Spec.map ((q s).2) ≫ B.fromSpecResidueField ((q s).1) = s
    rw [← SpecToEquivOfField_symm_apply]
    exact q.symm_apply_apply s
  have hdim : topologicalKrullDim B = (m : WithBot ℕ∞) := by
    change topologicalKrullDim (PrimeSpectrum (MvPolynomial (Fin m) K)) = _
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  have hlf : LocallyOfFiniteType b := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.2 inferInstance
  letI : IsIntegral B := inferInstance
  letI : Smooth b := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    letI : Algebra.Smooth K (MvPolynomial (Fin m) K) :=
      ⟨inferInstance, inferInstance⟩
    exact RingHom.smooth_algebraMap.mpr inferInstance
  letI : LocallyOfFiniteType b := hlf
  letI : QuasiCompact b := inferInstance
  letI : B.Over (Spec (.of K)) := ⟨b⟩
  letI : LocallyOfFiniteType (B ↘ Spec (.of K)) := hlf
  letI : QuasiCompact (B ↘ Spec (.of K)) := inferInstanceAs (QuasiCompact b)
  have hfinite := finite_trdeg_residueField (K := K) y
  obtain ⟨a, ha⟩ := Cardinal.lt_aleph0.mp hfinite
  have hge : m ≤ a := by
    have htr : residueFieldTrdeg b y = (a : Cardinal.{u}) := by
      unfold residueFieldTrdeg
      rw [residueFieldHomOfOver_eq]
      exact ha
    have hle : (m : Cardinal.{u}) ≤ (a : Cardinal.{u}) := by
      rw [← htr]
      exact hs
    exact_mod_cast hle
  have ha' : Algebra.trdeg K (B.residueField y) = (a : Cardinal.{u}) := ha
  let R := strictHenselizationRing s
  let g : Spec R ⟶ Spec (.of K) :=
    strictHenselizationStructuralMap s ≫ b
  let aR : K →+* R := (Spec.preimage g).hom
  letI : Algebra K R := aR.toAlgebra
  have hK : Spec.map (CommRingCat.ofHom (algebraMap K R)) = g := by
    exact Spec.map_preimage g
  have hmodel := smooth_strict_local_field_model_core K B b m a hdim Ω s y hy
    (_root_.AlgebraicGeometry.Scheme.Hom.specMap_residueFieldAlgebraMap b y) hΩ ha' hK
  obtain ⟨_, hlocal, hdomain, hdimR, he, _⟩ := hmodel
  letI := hlocal
  letI := hdomain
  have hdim0 : ringKrullDim R = 0 := by
    simpa [Nat.sub_eq_zero_of_le hge] using hdimR
  letI : Ring.KrullDimLE 0 (R : Type u) := Ring.krullDimLE_iff.mpr hdim0.le
  have hfieldR : IsField (R : Type u) := Ring.KrullDimLE.isField_of_isReduced
  letI : Field (R : Type u) := hfieldR.toField
  have hresinj : Function.Injective (IsLocalRing.residue (R : Type u)) :=
    (IsLocalRing.residue (R : Type u)).injective
  have hresbij : Function.Bijective (IsLocalRing.residue (R : Type u)) :=
    ⟨hresinj, IsLocalRing.residue_surjective⟩
  let eR : (R : Type u) ≃+* IsLocalRing.ResidueField (R : Type u) :=
    RingEquiv.ofBijective (IsLocalRing.residue (R : Type u)) hresbij
  let L := separableClosure (B.residueField y) Ω
  let e : (R : Type u) ≃+* L := eR.trans he
  exact ⟨L, inferInstance, IsSepClosure.sep_closed (B.residueField y),
    ⟨Scheme.Spec.mapIso e.symm.toCommRingCatIso.op⟩⟩

end AlgebraicGeometry.Scheme
