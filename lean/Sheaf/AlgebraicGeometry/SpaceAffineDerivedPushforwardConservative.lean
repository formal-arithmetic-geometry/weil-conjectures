/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q146
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite
import WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesQCoh
import WeilConjectures.AlgebraicGeometry.AffineDerivedPushforwardConservative
import Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Conservative affine derived direct image for algebraic spaces

Source: Stacks Project, spaces-perfect.tex, Tag 08II (lemma-affine-morphism) and
Tag 08FA (lemma-quasi-coherence-direct-image), part (1)
(blueprint: lem-sfb-space-affine-derived-pushforward-conservative).

The direct image is the K-injective right derived functor of the existing canonical
compatible-chart direct image on the equivalent small module models. Source and target
localization morphism universes are independent.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u wX wY

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- Affine derived direct image preserves quasi-coherent cohomology and reflects
isomorphisms between unbounded objects with quasi-coherent cohomology.
Source: Stacks Project, spaces-perfect.tex, Tags 08II and 08FA(1)
(blueprint: lem-sfb-space-affine-derived-pushforward-conservative).

Proof:
1. By lem-sfb-space-affine-locality choose a surjective etale scheme chart V of Y
   whose pullback X_V -> V is an affine scheme morphism. Its projection b to X is
   a surjective etale cover by lem-trf-space-fibre-products-etale-covers. By
   lem-sfb-space-derived-etale-chart-calculus, restriction preserves quasi-coherent
   cohomology and identifies the restriction of Rf_*K with R(f_V)_*b^*K.
2. The scheme map f_V is quasi-compact and quasi-separated by
   lem-weil-pbc-affine-morphism-permanence. Use
   lem-sfb-scheme-derived-etale-qcoh-comparison to identify its small-etale and
   Zariski direct images. The latter preserves quasi-coherent cohomology by
   lem-pc-derived-direct-image-preserves-qcoh. Descend quasi-coherence using the
   cover criterion of lem-sfb-space-derived-etale-chart-calculus. This proves
   landing without a boundedness assumption.
3. If Rf_*v is invertible, its restriction to V is invertible. The natural chart
   comparison and the scheme etale/Zariski equivalences identify it with the
   Zariski derived image of b^*v. Apply
   lem-sc-affine-derived-pushforward-conservative to conclude that b^*v is invertible.
4. Exact etale restriction commutes with every cohomology functor. The inverses of
   the restricted cohomology maps agree on overlaps by uniqueness and glue by the
   module sheaf axiom. Thus every cohomology map of v is invertible. Apply
   lem-weil-pbc-unbounded-derived-iso-cohomology. The argument also covers the
   empty space and its empty cover. -/
theorem affine_derivedDirectImage_preservesQCoh_and_reflectsIso
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (hf : MapIsAffine f)
    [HasDerivedCategory.{wX} X.SmallModules] [HasDerivedCategory.{wY} Y.SmallModules] :
    (∀ E : X.DerivedModules, X.derivedQCohProperty E →
      Y.derivedQCohProperty
        (((smallModuleDirectImage f).rightDerivedFunctor :
          X.DerivedModules ⥤ Y.DerivedModules).obj E)) ∧
    (∀ (E F : X.DerivedModules), X.derivedQCohProperty E → X.derivedQCohProperty F →
      ∀ v : E ⟶ F,
        IsIso (((smallModuleDirectImage f).rightDerivedFunctor :
          X.DerivedModules ⥤ Y.DerivedModules).map v) → IsIso v) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
