/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import Sheaf.AlgebraicGeometry.SpaceFaceRingedTotalCategory
public import Sheaf.AlgebraicGeometry.SpaceFppfHypercover
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import Sheaf.AlgebraicGeometry.HypercoverAugmentationFaceProperty
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFppfCoveringCalculus
import Sheaf.CategoryTheory.RingedHypercoverInjectiveAugmentationRing
import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
import WeilConjectures.Algebra.Homology.ExactCouple.DoubleComplex

/-! # Derived descent unit for a quasi-coherent module on a face total site

Source: Stacks Project, spaces-simplicial.tex, Tag 0DHE,
lemma-cohomological-descent-qcoh-for-fppf-hypercovering, with the injective-order-map
adaptation (blueprint: lem-sfb-fppf-face-heart-derived-unit).

The unit below is the localized ordinary adjunction unit followed by the canonical
K-injective right-derived comparison. Thus it names the actual derived adjunction
unit, rather than asserting only an isomorphism between its source and target.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u wZ wT

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace.SpaceFace

/-- The heart subcategory specified in the node: quasi-coherent components and
invertible tensor transitions for every injection.
Source: Stacks 0DHE (blueprint: lem-sfb-fppf-face-heart-derived-unit). -/
def IsCartesianQuasiCoherent {S : Scheme.{u}} {Z : AlgebraicSpace S}
    (U : SimplicialObject (Over Z)) (M : Modules U) : Prop :=
  (∀ n : SemiSimplexCategoryᵒᵖ,
    SheafOfModules.IsQuasicoherent ((evaluation U n).obj M)) ∧
  (∀ {n m : SemiSimplexCategoryᵒᵖ} (a : n ⟶ m), IsIso (transition U M a))

variable {S : Scheme.{u}} {Z : AlgebraicSpace S}
  (U : SimplicialObject (Over Z))
  [HasDerivedCategory.{wZ} Z.Modules] [HasDerivedCategory.{wT} (Modules U)]

/-- The canonical derived unit at a module placed in degree zero. The first arrow is
Q of the actual ordinary unit on complexes; the second is the existing right-derived
functor comparison computed by K-injectives. For an fppf hypercover the augmentation
pullback is exact, so this is G → Ru_*(u^*G).
Source: Stacks 0DHE (blueprint: lem-sfb-fppf-face-heart-derived-unit). -/
def derivedUnit (A : Augmentation U) (G : Z.Modules) :
    DerivedCategory.Q.obj ((CochainComplex.singleFunctor Z.Modules 0).obj G) ⟶
      A.direct.rightDerivedFunctor.obj
        (DerivedCategory.Q.obj ((A.inverse.mapHomologicalComplex (.up ℤ)).obj
          ((CochainComplex.singleFunctor Z.Modules 0).obj G))) :=
  DerivedCategory.Q.map ((A.adjunction.mapHomologicalComplex (.up ℤ)).unit.app
      ((CochainComplex.singleFunctor Z.Modules 0).obj G)) ≫
    A.direct.rightDerivedFunctorUnitQ ((A.inverse.mapHomologicalComplex (.up ℤ)).obj
      ((CochainComplex.singleFunctor Z.Modules 0).obj G))

/-- The canonical derived unit for a quasi-coherent module is invertible for an fppf
hypercover after forgetting degeneracies in the total site. All spaces are arbitrary.
Source: Stacks Project, spaces-simplicial.tex, Tag 0DHE, injective-order-map adaptation
(blueprint: lem-sfb-fppf-face-heart-derived-unit).

Proof:
1. By lem-sfb-hypercover-augmentation-face-property every augmentation and face is
flat, locally finitely presented and surjective. Component evaluation is exact and
conservative by lem-sfb-semisimplicial-ringed-total-category, so total pullback is exact.
These facts persist after base change to any etale V → Z. Put V_p = U_p ×_Z V.
2. Apply lem-sfb-flat-object-fppf-derived-sections to G restricted to V. One nonnegative
injective resolution J of its big-fppf section extension computes the small-etale
derived sections on V and on every V_p, compatibly with all flat face maps and the
augmentation. This is a comparison of derived diagrams, not only of cohomology groups.
3. By lem-sfb-space-fppf-covering-calculus the matching maps are fppf coverings. The
big site is subcanonical: maps into an algebraic space glue uniquely on scheme charts
by its fppf sheaf condition, and the equalities glue on overlaps. Apply
lem-sc-ringed-hypercover-injective-augmentation-ring to each injective J^q. Its augmented
alternating restriction row on V,V_0,V_1,... is exact and commutes with the differential.
4. The first-quadrant row spectral sequence of thm-sp-double-complex-spectral-sequences
identifies J(V) with the total of J^q(V_p) by the actual augmented restriction map.
Only finitely many p occur in each total degree, so no infinite convergence assumption
or bound on cohomological dimension enters.
5. By lem-sfb-face-total-derived-sections this total computes the derived sections
of Ru_*u^*G on V, and the augmented map is the map induced by derivedUnit. That node's
replacement compatibility identifies the chosen columns before cohomology. The source
and target are bounded below, since G and u^*G are modules in degree zero. Derived
sections over all etale V detect isomorphisms between these bounded-below objects,
so derivedUnit itself is invertible in the unbounded derived category. No compactness,
separation, affine face condition, or flatness of degeneracies is used. -/
theorem fppf_face_heart_derived_unit (hU : IsSpaceFppfHypercover U)
    (A : Augmentation U) (G : Z.Modules) (hG : SheafOfModules.IsQuasicoherent G) :
    IsIso (derivedUnit U A G) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace.SpaceFace
