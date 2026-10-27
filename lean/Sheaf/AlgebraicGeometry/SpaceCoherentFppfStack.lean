/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.AlgebraicGeometry.SpaceCoherentStackGeneral
public import Sheaf.CategoryTheory.SiteStackification
public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
import Sheaf.AlgebraicGeometry.SpaceModuleBaseChangeFlatProperSupport
import Sheaf.AlgebraicGeometry.SpaceChartTensorRealization
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFppfCoveringCalculus
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.Descent
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineChartCalculus
import Sheaf.AlgebraicGeometry.PointwiseModuleFlatnessBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import Sheaf.RingTheory.AnnihilatorFiniteFlatBaseChange
import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedIdealCorrespondence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality

/-! # Fppf descent of coherent families on algebraic spaces

Source: Stacks Project, quot.tex, Situation 08KB (situation-coherent),
Tags 08W5 (lemma-coherent-fibred-in-groupoids) and 08KC (lemma-coherent-stack)
(blueprint: lem-sfb-space-coherent-fppf-stack).

The already defined `CoherentModuli.category` retains actual modules, their base maps,
and the canonical tensor-pullback isomorphisms. The conclusion uses the existing
big-fppf total-category stack predicate, including descent of objects and arrows.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- Flat finitely presented quasi-coherent modules with proper support form an fppf stack.
Source: Stacks Project, quot.tex, Situation 08KB, Tags 08W5 and 08KC
(blueprint: lem-sfb-space-coherent-fppf-stack).

Proof:
1. For every test scheme T mapping to B, finite presentation of f makes X_T → T
   locally of finite type, by the chart base-change assertion of
   def-sfb-space-proper-quot-functor. Apply
   lem-sfb-space-module-base-change-flat-proper-support to every T' → T.
   Tensor pullback preserves all four module conditions without requiring T' → T flat.
2. Use lem-trf-space-chart-adjunction-tensor-realization for the canonical tensor
   comparisons. Multiplication on local tensors verifies their unit and associativity
   identities. Given two arrows to the same object and a compatible base arrow, the
   unique filler is the first isomorphism composed with the pullback of the inverse
   second isomorphism. This gives both fibred-groupoid lifting conditions of
   def-sfb-stable-pointed-moduli-groupoids.
3. The base maps of locally isomorphic objects agree because B is an fppf sheaf
   (def-trf-algebraic-space). By lem-sfb-space-fppf-covering-calculus the induced
   cover of X_T is fppf. Full faithfulness in lem-sfb-space-fppf-qcoh-descent glues
   module isomorphisms and their inverses uniquely, proving the isomorphism sheaf condition.
4. For object descent, first glue the maps T_i → B using the same sheaf condition.
   Sheaf fibre-product identities (lem-trf-space-fibre-products-etale-covers) identify
   the overlap modules as a descent datum on the induced fppf cover of X_T.
   Essential surjectivity in lem-sfb-space-fppf-qcoh-descent gives a quasi-coherent M
   and compatible isomorphisms to the given modules on the cover.
5. On an etale scheme chart U, pull the cover back to U. Use
   lem-trf-fppf-covering-is-fpqc, the tensor and Zariski-etale comparisons
   (lem-trf-space-chart-adjunction-tensor-realization and
   lem-trf-scheme-zariski-etale-quasi-coherent-equivalence), and
   lem-sfb-scheme-etale-module-exact-finiteness-comparison to identify the local modules.
   Clause (2) of lem-pc-fpqc-descent descends finite presentation. Apply
   lem-sfb-space-qcoh-affine-chart-calculus on every chart.
6. Every point of U lifts to the fppf cover by lem-sfb-space-fppf-covering-calculus.
   Through the same chart comparisons, clause (2) of
   lem-sfb-pointwise-module-flatness-base-change descends relative stalk flatness
   from the covering base local rings to the original base local ring.
7. Finite presentation gives finite type, so
   lem-sfb-space-module-proper-carrier-support defines the annihilator support Z.
   On an affine etale chart Spec A and an affine open Spec C of its pulled cover,
   lem-weil-pbc-flat-morphism-affine-criterion makes A → C flat. The tensor chart
   comparisons and lem-weil-pbc-module-pullback-affine-sections identify the pulled
   module with N tensor_A C. Apply lem-trf-annihilator-finite-flat-base-change.
   By lem-sfb-space-closed-ideal-correspondence and the image clause of
   lem-sfb-space-qcoh-affine-chart-calculus, the pulled closed ideal is Ann(N)C.
   Thus Z times_T T_i is exactly the annihilator support of M_i.
8. By lem-sfb-space-module-proper-carrier-support these pulled supports are proper.
   Their local-finite-type hypotheses follow from step 1. Properness descends by
   lem-sfb-space-flat-proper-fp-locality. The converse proper-carrier criterion
   supplies the finite type module on Z whose pushforward is M. The object from
   step 4 therefore satisfies all required conditions and realizes the descent datum.
   Together with steps 2 and 3 this is the existing IsFppfModuliStack condition. -/
theorem coherent_fppf_stack {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (hfp : ProperQuotFinitePresentation f) :
    IsFppfModuliStack (CoherentModuli.category f) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
