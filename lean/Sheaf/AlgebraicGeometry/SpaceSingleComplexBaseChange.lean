/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSingleComplexStalkCondition
public import Sheaf.AlgebraicGeometry.SpaceModuleDerivedExchange
public import Sheaf.AlgebraicGeometry.SpaceDerivedPullback
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
import Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.SpaceQcqsDistinguishedSquareInduction
import Sheaf.AlgebraicGeometry.DerivedEtaleZariskiEquivalence
import WeilConjectures.AlgebraicGeometry.SingleComplexQcqsInduction
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-! # Single-complex base change for algebraic spaces

Source: Stacks Project, spaces-perfect.tex, Tag 0DKH, with condition (1) of Tag 0DKG
and equation-bc preceding it (blueprint: lem-sfb-space-single-complex-base-change).

The geometric-stalk condition and the counit-mate exchange are the existing normalized
constructions. The conclusion concerns their specified composite in the unbounded
module derived category.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The geometric single-complex stalk condition implies qcqs direct-image base change.
Source: Stacks Project, spaces-perfect.tex, Tag 0DKH and equation-bc before Tag 0DKG
(blueprint: lem-sfb-space-single-complex-base-change).

Proof:
1. By lem-sfb-space-derived-etale-chart-calculus, restrict to affine etale charts of Y
   and then affine etale charts of the new base. The atlas and
   lem-trf-space-fibre-products-etale-covers give covers. Pullback composition respects
   the normalized adjunctions, so the restricted exchange is the same counit mate.
   By lem-sfb-space-stalk-condition-etale-charts the stalk hypothesis restricts.
   Exact restriction detects zero cohomology sheaves, so these reductions suffice.
   The restricted source is qcqs over the affine base.
2. For a qcqs etale algebraic space T over X, let P(T) mean invertibility of the same
   exchange followed by the restricted coefficient map. Pullback composition supplies
   that coefficient map, and lem-sfb-space-stalk-condition-etale-charts preserves its
   hypothesis. Use lem-sfb-space-qcqs-distinguished-square-induction for this property.
3. For affine T the whole square is a square of schemes. Transport the complexes and
   coefficient map using lem-sfb-derived-etale-zariski-equivalence. The adjunction and
   pullback composition comparisons identify the transported mate with the scheme mate.
   The chart stalk lemma supplies the ordinary stalk condition. Apply
   lem-pc-rf-single-complex-qcqs-induction and transport its conclusion back.
4. In an elementary distinguished square, lem-sfb-space-relative-mv-exchange-triangles
   gives a morphism of the relative Mayer-Vietoris triangles, with components the
   exchanges for W, U direct-sum V, and U times_W V, including the connecting square.
   The induction hypotheses make the last two components invertible; the inverse of
   their direct sum is the direct sum of inverses. Apply lem-sf-triangle-morphism-iso.
5. The induction gives P(X), using the identity restriction and unital comparisons.
   Undo the initial etale restrictions: the cohomology maps are isomorphisms on a
   covering, hence everywhere. This proves invertibility in the unbounded category.
No Tor-independence, properness, flatness, or boundedness hypothesis is used. -/
theorem singleComplexBaseChange_isIso {S : Scheme.{u}}
    [∀ Z : AlgebraicSpace S, HasDerivedCategory.{w} Z.SmallModules]
    {X X' Y Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (hqc : MapIsQuasiCompact f.hom.hom)
    (hqs : MapIsQuasiCompact (pullback.diagonal f.hom.hom))
    (K : X.DerivedModules) (hK : X.derivedQCohProperty K)
    (K' : X'.DerivedModules) (hK' : X'.derivedQCohProperty K')
    (φ : (spaceDerivedPullback g').obj K ⟶ K')
    (h_stalk : SingleComplex.StalkCondition f f' g g' sq K K' φ) :
    IsIso (moduleDerivedExchange f f' g g' sq.w K ≫ (derivedDirectImage f').map φ) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
