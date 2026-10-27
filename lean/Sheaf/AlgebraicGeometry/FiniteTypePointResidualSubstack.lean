/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q149
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties

import Sheaf.AlgebraicGeometry.EtaleSmoothAtlasFppfDescent
import Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.StackReducedLocallyNoetherianFppfDescent
import Mathlib.RingTheory.FinitePresentation

/-! # A locally finite type residual substack at a finite-type point

Source: Stacks Project, stacks-morphisms.tex, Tag 06G3, (1) implies (3), and
stacks-properties.tex, Tags 06MT and 06MU
(blueprint: lem-sfb-finite-type-point-residual-substack).

Point classes and their maps are the existing field-object quotient constructions.
The singleton source retains its groupoid automorphisms. Reducedness and local
Noetherianity are expressed by a smooth surjective scheme atlas with both properties.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry

namespace CategoryTheory

/-- A finite-type point has a reduced locally Noetherian singleton algebraic substack
whose inclusion is representable by algebraic spaces, fibrewise fully faithful and
locally of finite type. No Noetherian hypothesis is imposed on the base or target.
Source: Stacks Project, Tag 06G3, (1) implies (3), with Tags 06MT and 06MU
(blueprint: lem-sfb-finite-type-point-residual-substack).

Proof:
1. Choose the locally finite type field representative a : Spec L -> F. The etale
   stack condition and smooth atlas give fppf descent by
   lem-sfb-etale-smooth-atlas-fppf-descent. Diagonal representability makes a
   representable by spaces, by lem-sfb-stack-diagonal-space-source-representability.
   Form its self-relation R = Spec L x_F Spec L with the groupoid structure of
   lem-sfb-self-relation-quotient-embedding. Both projections are locally of finite
   type by lem-sfb-stack-chartwise-smooth-etale-calculus.
2. On etale affine charts of R these maps are finite type L-algebras. A field is
   Noetherian, so lem-weil-pbc-finite-type-noetherian-finite-presentation makes the
   algebras finitely presented. They are flat as vector spaces over L. Apply
   lem-sfb-space-local-properties-chart-test to obtain flat locally finitely
   presented projections.
3. The theorem lem-sfb-flat-groupoid-algebraic-quotient makes Z = [Spec L/R]
   algebraic, with representable surjective flat locally finitely presented cover q.
   It is an etale stack as well, since etale covers are fppf covers. The theorem
   lem-sfb-self-relation-quotient-embedding supplies a fibrewise fully faithful
   representable i : Z -> F with i q isomorphic to a.
4. Spec L is reduced and locally Noetherian. Apply
   lem-sfb-stack-reduced-locnoeth-fppf-descent to q to obtain the required reduced
   locally Noetherian smooth surjective scheme atlas of Z.
5. Spec L has exactly one point. The field-extension lifting property of q shows
   that Z has a nonempty singleton point set. The comparison i q isomorphic to a
   identifies its image with x, including when the representing field is extended.
6. Apply lem-sfb-representable-lft-fppf-source-descent to q and i: the composite
   i q is locally of finite type and q is surjective flat locally finitely
   presented, so i is locally of finite type. None of these steps assumes the
   base or F Noetherian. -/
theorem exists_finiteTypePoint_residualSubstack {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsAlgebraicModuliStack F)
    (x : ModuliPoints F)
    (hfinite : ∃ (L : Type u) (_ : Field L) (b : Spec (.of L) ⟶ S)
      (a : BasedFunctor (discreteModuli (yoneda.obj (Over.mk b))) F),
      ModuliSpaceTest (@LocallyOfFiniteType) a ∧ x ∈ Set.range (moduliPointMap a)) :
    ∃ (Z : BasedCategory.{v, w} (Over S)) (i : BasedFunctor Z F),
      IsAlgebraicModuliStack Z ∧ IsRepresentableByAlgebraicSpaces i ∧
      (∀ T : Over S, (moduliFiberMap i T).Full ∧ (moduliFiberMap i T).Faithful) ∧
      ModuliSpaceTest (@LocallyOfFiniteType) i ∧
      (∃ (U : Over S) (q : BasedFunctor (discreteModuli (yoneda.obj U)) Z),
        IsSmoothModuliAtlas Z U q ∧ IsReduced U.left ∧ IsLocallyNoetherian U.left) ∧
      Nonempty (Unique (ModuliPoints Z)) ∧ Set.range (moduliPointMap i) = {x} := by
  sorry

end CategoryTheory
