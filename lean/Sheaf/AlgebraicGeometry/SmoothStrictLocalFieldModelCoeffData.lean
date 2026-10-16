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
  sorry

end Scheme
end AlgebraicGeometry
