/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import WeilConjectures.Mathlib.Topology.KrullDimension

import Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModelCore
import Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModelCoeff

/-! # Coefficient fields of smooth strict localizations

Source: blueprint, sec-smooth-purity/sk-prop-sf-cbc/thm-sc-affine-torsion-cd,
local calculation in dimension d; Stacks Tags 04GG, 04GP, 06LN, 06LK, 00P1.
(blueprint: lem-sc-smooth-strict-local-field-model)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A smooth integral strict localization has a separably closed coefficient field.
Source: blueprint thm-sc-affine-torsion-cd, local calculation in dimension d;
Stacks Tags 04GG, 04GP, 06LN, 06LK, 00P1.
(blueprint: lem-sc-smooth-strict-local-field-model)

Proof: choose a smooth finite-type affine chart at y and identify its localized
pointed-etale colimit with the strict henselization of the stalk. Its residue field
is the relative separable closure in Ω. Smoothness gives regularity of the stalk;
strict henselization preserves regularity and dimension, and regular local rings
are domains. Faithful flatness embeds the stalk and hence the function field.
The finite-type point dimension formula gives dim R = d - a, while the generic
point calculation gives trdeg K K(Y) = d. The affine ind-etale presentation shows
every fraction in R is algebraic over K(Y): represent numerator and denominator
at one stage and use its finite separable residue field at the kernel in Frac R.
Choose a separating transcendence basis of κ(y)/K and lift it to R. Every nonzero
polynomial in these lifts is a unit, embedding the rational-function field.
The relative separable closure of this field is precisely the residue field.
For each finite separable subextension, a primitive element has a simple minimal
polynomial; henselian lifting gives its prescribed residual root. Simple-root
uniqueness makes all finite-stage embeddings compatible. Their union gives a
coefficient field whose reduction is bijective and whose transcendence degree is a.
Finally the transcendence-degree tower formula gives trdeg F Frac R = d - a. -/
theorem smooth_strict_local_field_model
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
      strictHenselizationStructuralMap s ≫ f) :
    IsRegularLocalRing (strictHenselizationRing s) ∧
    ∃ hlocal : IsLocalRing (strictHenselizationRing s),
      ∃ hdomain : IsDomain (strictHenselizationRing s),
        letI := hlocal
        letI := hdomain
        ringKrullDim (strictHenselizationRing s) = ((d - a : ℕ) : WithBot ℕ∞) ∧
        ∃ e : IsLocalRing.ResidueField (strictHenselizationRing s) ≃+*
            separableClosure (Y.residueField y) Ω,
          Spec.map (CommRingCat.ofHom
            ((separableClosure (Y.residueField y) Ω).subtype.comp
              (e.toRingHom.comp (IsLocalRing.residue (strictHenselizationRing s))))) ≫
            strictHenselizationStructuralMap s = s ∧
          ∃ i : Y.functionField →+* FractionRing (strictHenselizationRing s),
            Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk (genericPoint Y) =
              Spec.map (CommRingCat.ofHom
                (algebraMap (strictHenselizationRing s)
                  (FractionRing (strictHenselizationRing s)))) ≫
                strictHenselizationStructuralMap s ∧
            (letI := i.toAlgebra
             Algebra.IsAlgebraic Y.functionField (FractionRing (strictHenselizationRing s))) ∧
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
  obtain ⟨hreg, hlocal, hdomain, hdim, he, hres, i, hi, halg⟩ :=
    smooth_strict_local_field_model_core K Y f d a hd Ω s y hy hκ hΩ ha hK
  let := hlocal
  let := hdomain
  obtain ⟨F, hfield, hKF, j, hsep, hbij, htr, htrQ⟩ :=
    smooth_strict_local_field_model_coeff K Y f d a hd Ω s y hy hκ hΩ ha hK
  exact ⟨hreg, hlocal, hdomain, hdim, he, hres, i, hi, halg,
    ⟨F, hfield, hKF, j, hsep, hbij, htr, htrQ⟩⟩

end AlgebraicGeometry.Scheme
