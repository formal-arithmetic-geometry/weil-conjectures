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
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModelCore
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import WeilConjectures.PointCount

/-! # Fraction-field transcendence degree interface

Source: blueprint thm-sc-affine-torsion-cd, local calculation in dimension d;
Stacks Tags 030H and 0A21.

This is the dimension and transcendence-degree part of the coefficient-field
argument, after a coefficient field and its residue section have been supplied.
(blueprint: new-lem-sc-smooth-strict-local-field-model-coeff-fraction-trdeg)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

private theorem functionField_trdeg_of_dimension
    (K : Type u) [Field K] (Y : Scheme.{u}) [IsIntegral Y]
    (f : Y ⟶ Spec (.of K)) [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) (hd : topologicalKrullDim Y = (d : WithBot ℕ∞))
    [Algebra K Y.functionField]
    (h : Spec.map (CommRingCat.ofHom (algebraMap K Y.functionField)) =
      Y.fromSpecStalk (genericPoint Y) ≫ f) :
    Algebra.trdeg K Y.functionField = (d : Cardinal) := by
  let : Y.Over (Spec (.of K)) := ⟨f⟩
  let : LocallyOfFiniteType (Y ↘ Spec (.of K)) := ‹LocallyOfFiniteType f›
  let : QuasiCompact (Y ↘ Spec (.of K)) := ‹QuasiCompact f›
  obtain ⟨n, hn, ht⟩ := topologicalKrullDim_closed_irreducible_eq_trdeg
    (K := K) (X := Y) Set.univ isClosed_univ
    (IrreducibleSpace.isIrreducible_univ Y) (genericPoint Y) (Set.mem_univ _)
    (genericPoint_spec Y)
  have hdim : topologicalKrullDim (Set.univ : Set Y) = topologicalKrullDim Y :=
    (Homeomorph.Set.univ Y).isHomeomorph.topologicalKrullDim_eq _
  have hnd : n = d := by
    rw [hdim, hd] at hn
    exact_mod_cast hn.symm
  subst n
  let : Algebra K (Y.residueField (genericPoint Y)) :=
    (f.residueFieldAlgebraMap (genericPoint Y)).toAlgebra
  let e : Y.functionField ≃ₐ[K] Y.residueField (genericPoint Y) :=
    { RingEquiv.ofBijective (Y.residue (genericPoint Y)).hom
        ⟨(Y.residue (genericPoint Y)).hom.injective, Y.residue_surjective _⟩ with
      commutes' c := by
        have he : CommRingCat.ofHom (algebraMap K Y.functionField) ≫
            Y.residue (genericPoint Y) =
            CommRingCat.ofHom (f.residueFieldAlgebraMap (genericPoint Y)) := by
          apply Spec.map_injective
          rw [Spec.map_comp, h, f.specMap_residueFieldAlgebraMap]
          rw [← Category.assoc]
          rfl
        exact congrArg (fun g ↦ g.hom c) he }
  exact e.trdeg_eq.trans ht

/-- Compute the transcendence degree of the fraction field over a coefficient field.

Source: blueprint, sec-smooth-purity/sk-prop-sf-cbc/thm-sc-affine-torsion-cd,
local calculation in dimension d; Stacks Tags 030H and 0A21.
(blueprint: new-lem-sc-smooth-strict-local-field-model-coeff-fraction-trdeg)

Proof: the generic-point dimension formula gives transcendence degree d for the
function field of Y.  The core theorem supplies an algebraic embedding of that
function field into the fraction field of the strict henselization, so the
latter also has transcendence degree d over K.  Apply the tower formula to
K ⊂ F ⊂ Frac(R), where the supplied coefficient field has transcendence degree
a over K, and subtract the finite cardinals to obtain d - a.
-/
theorem smooth_strict_local_field_model_coeff_fraction_trdeg
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
    [IsLocalRing (strictHenselizationRing s)]
    [IsDomain (strictHenselizationRing s)]
    (F : Type u) [Field F] [Algebra K F]
    (j : F →ₐ[K] strictHenselizationRing s)
    (htr : Algebra.trdeg K F = (a : Cardinal)) :
    (letI := ((algebraMap (strictHenselizationRing s)
        (FractionRing (strictHenselizationRing s))).comp j.toRingHom).toAlgebra
     Algebra.trdeg F (FractionRing (strictHenselizationRing s)) =
       ((d - a : ℕ) : Cardinal)) := by
  classical
  let R := strictHenselizationRing s
  let Q := FractionRing R
  let : Algebra K Q := inferInstance
  let : IsScalarTower K R Q := inferInstance
  obtain ⟨_, hl, hdom, _, e, he, i, hi, halg⟩ :=
    smooth_strict_local_field_model_core K Y f d a hd Ω s y hy hκ hΩ ha hK
  let kY : K →+* Y.functionField :=
    (Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ f)).hom
  let : Algebra K Y.functionField := kY.toAlgebra
  have hkY : Spec.map (CommRingCat.ofHom (algebraMap K Y.functionField)) =
      Y.fromSpecStalk (genericPoint Y) ≫ f := Spec.map_preimage _
  have htY := functionField_trdeg_of_dimension K Y f d hd hkY
  let : Algebra Y.functionField Q := i.toAlgebra
  have htower : IsScalarTower K Y.functionField Q := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro c
    have hm : CommRingCat.ofHom (i.comp kY) =
        CommRingCat.ofHom (algebraMap K Q) := by
      apply Spec.map_injective
      change Spec.map (CommRingCat.ofHom kY ≫ CommRingCat.ofHom i) = _
      rw [Spec.map_comp]
      change Spec.map (CommRingCat.ofHom i) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K Y.functionField)) = _
      rw [hkY, ← Category.assoc, hi, Category.assoc, ← hK, ← Spec.map_comp]
      congr 1
    exact congrArg (fun g ↦ g.hom c) hm.symm
  let := htower
  let := halg
  have htQ : Algebra.trdeg K Q = (d : Cardinal) := by
    have ht := trdeg_add_eq (R := K) (S := Y.functionField) (A := Q)
    rw [trdeg_eq_zero (R := Y.functionField), add_zero, htY] at ht
    exact ht.symm
  let : Algebra F Q := ((algebraMap R Q).comp j.toRingHom).toAlgebra
  have : IsScalarTower K F Q := by
    apply IsScalarTower.of_algebraMap_eq'
    ext c
    exact congrArg (algebraMap R Q) (j.commutes c).symm
  have ht := trdeg_add_eq (R := K) (S := F) (A := Q)
  rw [htr, htQ] at ht
  have hfinite : Algebra.trdeg F Q < Cardinal.aleph0 := by
    apply lt_of_le_of_lt (show Algebra.trdeg F Q ≤ (a : Cardinal) +
      Algebra.trdeg F Q from le_add_self)
    rw [ht]
    exact Cardinal.natCast_lt_aleph0
  obtain ⟨b, hb⟩ := Cardinal.lt_aleph0.mp hfinite
  rw [hb, ← Nat.cast_add] at ht
  have hab : a + b = d := by exact_mod_cast ht
  change Algebra.trdeg F Q = _
  rw [hb]
  congr 1
  omega

end Scheme
end AlgebraicGeometry
