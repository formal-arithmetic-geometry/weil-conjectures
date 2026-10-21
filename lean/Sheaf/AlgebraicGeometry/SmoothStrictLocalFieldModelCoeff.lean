/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import WeilConjectures.Mathlib.Topology.KrullDimension

import Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModelCoeffData
import Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModelCoeffFractionTrdeg

/-! # Coefficient fields of a smooth strict localization

Source: blueprint, sec-smooth-purity/sk-prop-sf-cbc/thm-sc-affine-torsion-cd,
local calculation in dimension d; Stacks Tags 04HX, 04GP, 06LN, 06LK and 04GG.
(blueprint: lem-sc-smooth-strict-local-field-model-coeff)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A coefficient field and its transcendence degrees in a smooth strict localization.
Source: blueprint thm-sc-affine-torsion-cd, local calculation in dimension d;
Stacks Tags 04HX, 04GP, 04GG, 06RR, 030N, 030H and 0A21.
(blueprint: lem-sc-smooth-strict-local-field-model-coeff)

Proof: use the core theorem's residue comparison to identify the residue field
with l = separableClosure (Y.residueField y) Omega. The three structural Spec
identities make reduction followed by this comparison a K-algebra map.
The point residue extension is essentially of finite type over the perfect
field K, so it has a finite separating transcendence basis. Lift this family
through reduction. Nonzero polynomial evaluations have nonzero residue and
are units, so evaluation extends to the rational function field. The remaining
residue extension is separable algebraic and hence ind-etale. The existing
henselian-colimit theorem gives its compatible section into R; this is the
proved coefficient-section helper used by the coefficient-data theorem.
Take F = l with this section j. The field F is separably closed, reduction
composed with j is the inverse of the residue comparison, and algebraicity
over the point residue field gives trdeg_K F = a.

For the fraction-field calculation, the closed-irreducible dimension formula
at the generic point gives trdeg_K Y.functionField = d. The generic stalk is
already a field, and its residue map is an isomorphism. The core's structural
algebraic embedding into Q = Frac(R) is K-linear, so the tower formula gives
trdeg_K Q = d. The tower K -> F -> Q then gives a + trdeg_F Q = d.
This forces trdeg_F Q to be a finite cardinal, and finite-cardinal arithmetic
gives trdeg_F Q = d-a. Assemble this equality with the coefficient-field data. -/
theorem smooth_strict_local_field_model_coeff
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
    [IsDomain (strictHenselizationRing s)] :
    ∃ (F : Type u) (_ : Field F) (_ : Algebra K F),
      ∃ j : F →ₐ[K] strictHenselizationRing s,
        IsSepClosed F ∧
        Function.Bijective ((IsLocalRing.residue (strictHenselizationRing s)).comp
          j.toRingHom) ∧
        Algebra.trdeg K F = (a : Cardinal) ∧
        (letI := ((algebraMap (strictHenselizationRing s)
            (FractionRing (strictHenselizationRing s))).comp j.toRingHom).toAlgebra
         Algebra.trdeg F (FractionRing (strictHenselizationRing s)) =
           ((d - a : ℕ) : Cardinal)) := by
  obtain ⟨F, hF, hKF, j, hsep, hbij, htr⟩ :=
    exists_smooth_strict_local_field_coeff_data K Y f d a hd Ω s y hy hκ hΩ ha hK
  have htrQ := smooth_strict_local_field_model_coeff_fraction_trdeg K Y f d a hd Ω s y hy
    hκ hΩ ha hK F j htr
  exact ⟨F, hF, hKF, j, hsep, hbij, htr, htrQ⟩

end Scheme
end AlgebraicGeometry
