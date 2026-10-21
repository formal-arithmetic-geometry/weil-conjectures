/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Integral
import WeilConjectures.AlgebraicGeometry.RelativelyFlatModulePullback
import WeilConjectures.AlgebraicGeometry.FlatInvertibleSectionsTorsionFree
import Sheaf.AlgebraicGeometry.GeometricallyReducedEtaNormal
import Sheaf.TraceFormula.FlatDenseGenericFibrePureDimension
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Sheaf.TraceFormula.GeometricReducedFibreLocusBaseChange
import Sheaf.TraceFormula.ReducedFibreModification

/-!
# Finite normalization of a generically smooth curve over a separably closed valuation base

Source: literature/temkin-stable-modification-arXiv-0707.3953v3.pdf, Section 4.1,
opening paragraph, printed p. 25 (blueprint: lem-trf-valuation-curve-finite-normalization).
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- Finite normalization of a generically smooth curve over a separably closed valuation base.

Source: Temkin, Stable modification of relative curves, Section 4.1, opening paragraph,
printed p. 25 (blueprint: lem-trf-valuation-curve-finite-normalization).

Proof plan, following the seven steps of the DAG node:

1. The valuation condition makes V and its localizations normal. By
   `lem-sc-flat-invertible-sections-torsion-free` and
   `lem-weil-pbc-localization-base-change`, nonempty affine sections inject into their
   nonzero generic localizations. Thus the generic fibre is integral, nonempty and dense,
   and f is dominant.
2. The smooth generic curve is normal by `lem-sc-smooth-normal` and geometrically reduced
   by `sbc-lem-smooth-geometrically-reduced`. Apply `lem-trf-reduced-fibre-modification`.
   Its altered base has finite separable generic field extension, hence K itself by
   `def-kun-separably-closed`.
3. `lemma-nagata-proper-valuative-criterion-existence-api` extends the generic point to
   a valuative section. Pulling the finite modification back along this section gives
   a finite morphism h : Y → X, unchanged generically. Finite presentation, flatness and
   geometrically reduced fibres follow from `lem-weil-pbc-qcqs-morphism-permanence`,
   `lem-pc-relatively-flat-module-pullback`, and
   `lem-trf-geometric-reduced-fibre-locus-base-change`.
4. For every nonempty affine in Y, flatness embeds its ring B in the nonzero domain B_K.
   The generic fibre is dense and irreducible, so Y is integral. Affine restrictions are
   finitely presented by `lem-weil-pbc-qcqs-morphism-permanence`. Apply
   `lem-trf-geometrically-reduced-eta-normal` to each such affine restriction.
5. If b in Frac(B) is integral over B, generic normality gives b in B_K, so b = c/a with
   nonzero a in V. The finite algebra B[b] defines a proper finite eta-modification,
   by `lem-weil-pbc-finite-proper`, which is an isomorphism by step 4. Therefore b lies
   in B. `lem-weil-pbc-integral-closure-commutes-localization` makes all stalks normal.
6. Above a nonempty affine Spec A in X, the finite ring B of Y lies in the integral
   closure of A in k(X), by `lem-weil-pbc-finite-algebra-is-integral`. Conversely its
   normality puts that integral closure in B. These identifications agree on restrictions
   by `lem-weil-pbc-integral-closure-commutes-localization`, so `def-sc-normalization`
   identifies h with X.fromNormalization. It is finite and unchanged generically, and
   its source is normal, flat and finitely presented over the base.
7. By `lem-weil-pbc-finite-proper` and `def-weil-proper-morphism`, the normalization has
   closed image. The image contains the dense generic fibre, so it is surjective. Apply
   `lem-trf-flat-dense-generic-fibre-pure-dimension` with d = 1 to obtain the stated pure
   dimension of every nonempty fibre. Empty fibres impose no condition.
-/
theorem finite_normalization_of_valuation_curve
    (V K : Type u) [CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K]
    [IsSepClosed K]
    (hval : ∀ a : K, a ≠ 0 →
      a ∈ Set.range (algebraMap V K) ∨ a⁻¹ ∈ Set.range (algebraMap V K))
    (hfinite : Set.Finite {p : Ideal V | p.IsPrime})
    (hchain : ∀ (p q : Ideal V), p.IsPrime → q.IsPrime → p ≤ q ∨ q ≤ p)
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of V)) [IsIntegral X]
    [Flat f] [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (hpure : ∀ y : Spec (CommRingCat.of V),
      (Nonempty (f.fiber y) →
        ∀ C ∈ irreducibleComponents (f.fiber y : Type u),
          topologicalKrullDim C = (1 : WithBot ℕ∞)))
    [Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap V K))))] :
    IsFinite X.fromNormalization ∧
      Surjective X.fromNormalization ∧
      IsIso (pullback.map (X.fromNormalization ≫ f)
        (Spec.map (CommRingCat.ofHom (algebraMap V K))) f
        (Spec.map (CommRingCat.ofHom (algebraMap V K))) X.fromNormalization
        (𝟙 _) (𝟙 _) (by simp) (by simp)) ∧
      (∀ x : X.normalization,
        IsDomain (X.normalization.presheaf.stalk x) ∧
          IsIntegrallyClosed (X.normalization.presheaf.stalk x)) ∧
      Flat (X.fromNormalization ≫ f) ∧
      LocallyOfFinitePresentation (X.fromNormalization ≫ f) ∧
      QuasiCompact (X.fromNormalization ≫ f) ∧
      QuasiSeparated (X.fromNormalization ≫ f) ∧
      (∀ y : Spec (CommRingCat.of V),
        (Nonempty ((X.fromNormalization ≫ f).fiber y) →
          ∀ C ∈ irreducibleComponents
              ((X.fromNormalization ≫ f).fiber y : Type u),
            topologicalKrullDim C = (1 : WithBot ℕ∞))) := by
  sorry

end AlgebraicGeometry
