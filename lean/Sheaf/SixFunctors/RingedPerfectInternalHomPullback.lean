/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
public import Sheaf.SixFunctors.RingedDerivedAdjointLift
public import Sheaf.Paper.RingedPullbackHomEvaluationComparison
import Sheaf.CategoryTheory.RingedSitePerfectDuality
import Sheaf.CategoryTheory.ClosedEvaluationDualCriterion
import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.Comparison

/-! # Perfect-source internal Hom under derived ringed-topos pullback

Source: Stacks Project, Cohomology on Sites, Tags 08JH, 08H3 and 08JJ;
Cohomology, Tag 0GM7(1), in its evaluation-normalized ringed-topos form.
(blueprint: lem-sfb-ringed-perfect-internal-hom-pullback).

The comparison is the existing transpose of pulled-back evaluation. The tensor
comparison and derived pullback retain their K-flat normalization. The first
argument is locally perfect; the second belongs to the unbounded derived category.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures

namespace CategoryTheory.RingedDerivedComparisons

/-- The evaluation-defined internal-Hom pullback comparison is an isomorphism
for a locally perfect first variable, naturally in both variables.

Source: Stacks Project, Tags 08JH, 08H3 and 08JJ; Tag 0GM7(1).
(blueprint: lem-sfb-ringed-perfect-internal-hom-pullback).

Here `X` presents the source ringed topos and `Y` the target. The fixed `Site`
presentations carry the ordinary unbounded derived categories and their signed
K-flat tensor models. `AdjointLift f` identifies its pullback with the derived
scalar-extension pullback of the given geometric ringed-topos morphism. The map
`ringedPullbackHomComparison` is, by definition, the right-tensor transpose of
`pullbackHomTensorator` followed by the image of evaluation. Thus the assertion
concerns the prescribed comparison, rather than an unspecified isomorphism.

Proof of the accepted split:
1. Use `lem-sf-ringed-derived-closed-symmetric-monoidal` on both categories.
   For perfect P, `lem-sfb-ringed-site-perfect-duality` identifies RHom(P,N)
   with D tensor N for every unbounded N, where D = RHom(P,R). Use symmetry
   to express its evaluation in the left-tensor adjunction convention.
2. Apply `lem-fix-closed-evaluation-dual-criterion`: transposing the unitor
   and applying the inverse evaluation comparison gives the coevaluation.
   Both triangle identities hold globally, without a global perfect model.
3. The canonical pullback is symmetric strong monoidal by
   `lem-sfb-ringed-derived-monoidal-comparisons`. Apply
   `lem-fix-monoidal-dual-hom-comparison` to this dual pair and arbitrary Q.
4. Convert its left-tensor transpose to the right-tensor convention.
   Symmetric monoidality moves the braiding through the tensorator;
   the two successive symmetries cancel. Adjunction injectivity identifies
   that invertible comparison with `ringedPullbackHomComparison`.
5. Untranspose the naturality square. Naturality of the tensorator and
   evaluation identifies its two composites. Restrict the first variables
   to the locally perfect objects. No flatness or bound on Q is used.
-/
theorem ringedPerfectInternalHomPullback {X Y : Site.{u, w}}
    [HasSheafify Y.J AddCommGrpCat.{u}]
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ U : Y.C, HasSheafify (Y.J.over U) AddCommGrpCat.{u}]
    [∀ U : Y.C, (Y.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {f : Morphism X Y} (l : AdjointLift f) :
    (∀ P : Y.D, SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w} Y.A P →
      ∀ Q : Y.D, IsIso (ringedPullbackHomComparison l P Q)) ∧
    (∀ P P' Q Q' : Y.D,
      SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w} Y.A P →
      SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w} Y.A P' →
      ∀ (a : P' ⟶ P) (b : Q ⟶ Q'),
      l.edge.left.map ((pullbackHomFunctor Y).map (Prod.mkHom a.op b)) ≫
          ringedPullbackHomComparison l P' Q' =
        ringedPullbackHomComparison l P Q ≫
          (pullbackHomFunctor X).map
            (Prod.mkHom (l.edge.left.map a).op (l.edge.left.map b))) :=
  sorry

end CategoryTheory.RingedDerivedComparisons
