/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.KrullDimension
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange
import Sheaf.AlgebraicGeometry.IndEtaleStrictLocalInvariance
import Sheaf.AlgebraicGeometry.StrictBaseClosedPointLocalizations
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import Sheaf.Paper.StrictHenselizationFunctoriality
import Sheaf.TraceFormula.FiniteProjectiveEnvelope
import Sheaf.TraceFormula.LocalQuasiFiniteProjection
import WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.Topology.DimensionSupremumLocalDimensions
import WeilConjectures.AlgebraicGeometry.StrictHenselization

/-!
# Dimension-preserving projective model of a strict localization

Source: Orgogozo, “Modifications et cycles proches sur une base générale”, Proposition 2.3,
printed p. 4 in the author version (blueprint: lem-trf-bounded-dimension-projective-local-model).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A bounded-fibre locally finite type morphism admits a projective model of each strict
localization with the same fibre bound.

Source: Orgogozo, “Modifications et cycles proches sur une base générale”, Proposition 2.3,
proof, printed p. 4 (blueprint: lem-trf-bounded-dimension-projective-local-model).

Proof:
1. Base change `f` to the strict henselization `B` at `x ≫ f`. By
   `lem-sc-fibre-dimension-after-base-change` and `def-pc-scheme-fibre`, fibre dimensions are
   preserved; `lem-weil-pbc-dimension-supremum-local-dimensions` and `def-kun-dimension` pass
   from local to global dimension. The strict-localization comparison
   `lem-weil-pbc-strict-base-closed-point-localizations`, using
   `lem-weil-pbc-strict-henselization-functoriality` and
   `def-weil-pbc-strict-henselization-limit`, identifies the resulting localization with `X_(x)`.
2. `lem-trf-local-quasi-finite-projection` gives an affine neighbourhood and a separated
   quasi-finite finite-type map to affine `d`-space, with `d ≤ N`; the target is affine by
   `def-nagata-relative-affine-space` and the base is the affine scheme from
   `def-weil-pbc-strict-henselization-limit`.
3. `thm-pqf-zmt-factorization` factors this map as an open immersion followed by a finite map.
4. `lem-trf-finite-projective-envelope` embeds the finite factor into a projective proper `B`-
   scheme whose fibres have dimension at most `d`, hence at most `N`; the conclusion uses
   `def-pc-projective-morphism` and `def-weil-proper-morphism`.
5. `lem-trf-ind-etale-strict-local-invariance` identifies strict localizations across the two
   open immersions, and `def-weil-geometric-point` supplies the pointed image `y`. Composing
   with the canonical map `strictHenselizationMap` from
   `lem-weil-pbc-strict-henselization-functoriality` gives the displayed isomorphism over `B`.
-/
theorem exists_boundedDimension_projective_local_model
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (N : ℕ) (hN : ∀ s : S,
      topologicalKrullDim (f.fiber s) ≤ (N : WithBot ℕ∞))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) :
    ∃ (P : Scheme.{u}) (p : P ⟶ Scheme.strictHenselizationScheme (x ≫ f)),
      IsProjective p ∧ IsProper p ∧
      ∃ (y : Spec (.of Ω) ⟶ P),
        (y ≫ p) (IsLocalRing.closedPoint Ω) =
          (Spec.map (CommRingCat.ofHom
            (Scheme.strictHenselizationPointEvaluation (x ≫ f)))
            (IsLocalRing.closedPoint Ω)) ∧
        ∃ (θ : Scheme.strictHenselizationScheme x ≅ Scheme.strictHenselizationScheme y),
          θ.hom ≫ Scheme.strictHenselizationStructuralMap y ≫ p =
            Scheme.strictHenselizationMap f x ∧
          ∀ s : Scheme.strictHenselizationScheme (x ≫ f),
            topologicalKrullDim (p.fiber s) ≤ (N : WithBot ℕ∞) := by
  sorry

end AlgebraicGeometry
