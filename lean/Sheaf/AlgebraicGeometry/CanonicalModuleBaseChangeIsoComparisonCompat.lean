/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedModuleBaseChangeMap

import Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
import Sheaf.AlgebraicGeometry.ModulePullbackComparisonTargetAutomorphism

/-! # Coordinate compatibility with a prescribed module comparison

Source: Stacks Project, Tags 06YJ, 08HY, 0D5T and 08IB.
(blueprint: stage3-canonicalModuleBaseChange_iso_comparison_ab).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry

/-- Coordinate-change isomorphisms identify the canonical module base-change maps.
Source: Stacks Project, Tag 08HY, counit construction and coordinate transport;
Tag 0D5T, composition of derived functors.
(blueprint: stage3-canonicalModuleBaseChange_iso_comparison_ab).

Proof: Identify the given cartesian square with the chosen pullback square using
the coordinate isomorphisms. Derived pullback and direct-image composition,
together with cancellation of the inverse coordinates, give the source
isomorphism a0. The pullback isomorphism and ordinary tensor-pullback composition
identify the pulled-back modules; applying the single functor and derived
direct-image composition gives the target isomorphism b0. Transpose the two
base-change maps under the derived adjunction for the second projection. By
pullback composition and naturality of the counit, both transposes are the
pullback of the same counit of f after inverse coordinates cancel. Injectivity
of the adjunction Hom equivalence identifies these mates. First use compatible
counits to transport c to a comparison cT on the chosen
pullback. Mate naturality then gives the equation with a0, b0 and cT. The
predicate on c0 only asserts existence of a left-derived counit; it does not
pin it to the counit transported from hc. Apply
modulePullbackComparison_target_automorphism to c0 and cT: there is an ordinary
module automorphism alpha with cT = c0 followed by alpha[0]. Write d for the
image of alpha[0] under Rq_* and then T; d is an automorphism of the transported
target. Replace b0 by b0 followed by d.inv, and take a = a0. Functoriality and
cancellation of d.hom followed by d.inv give precisely the required equation.
Thus the assertion holds for every comparison c0, including when G is zero
or the schemes are empty. No flatness of G or affine hypothesis is used.
-/
theorem canonicalModuleBaseChange_iso_comparison_ab
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (a : Y ⟶ Z), (Scheme.Modules.tensorPullback a).Additive]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (g' : X' ⟶ X) (f' : X' ⟶ S') (sq : IsPullback g' f' f g)
    (G : X.Modules)
    (c : (derivedPullback g').obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback g').obj G))
    (hc : IsDerivedModulePullbackComparison g' G c)
    {A B : Scheme.{u}} (eS : S ≅ A) (eT : S' ≅ B)
    (c0 : (derivedPullback (pullback.fst (f ≫ eS.hom)
      (eT.inv ≫ g ≫ eS.hom))).obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ⟶
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings (pullback (f ≫ eS.hom)
          (eT.inv ≫ g ≫ eS.hom)).toRingedSpace)) 0).obj
        ((Scheme.Modules.tensorPullback (pullback.fst (f ≫ eS.hom)
          (eT.inv ≫ g ≫ eS.hom))).obj G))
    (hc0 : IsDerivedModulePullbackComparison
      (pullback.fst (f ≫ eS.hom) (eT.inv ≫ g ≫ eS.hom)) G c0) :
  let fA := f ≫ eS.hom
      let gA := eT.inv ≫ g ≫ eS.hom
      let E := (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G
      let T := schemeDerivedDirectImage eT.inv
      ∃ a : (derivedPullback g).obj ((schemeDerivedDirectImage f).obj E) ≅
            T.obj ((derivedPullback gA).obj ((schemeDerivedDirectImage fA).obj E)),
        ∃ b : (schemeDerivedDirectImage f').obj
              ((DerivedCategory.singleFunctor
                (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).obj
                  ((Scheme.Modules.tensorPullback g').obj G)) ≅
            T.obj ((schemeDerivedDirectImage (pullback.snd fA gA)).obj
              ((DerivedCategory.singleFunctor
                (SheafOfModules.{u} (moduleRings (pullback fA gA).toRingedSpace)) 0).obj
                  ((Scheme.Modules.tensorPullback (pullback.fst fA gA)).obj G))),
          (schemeDerivedBaseChangeMap f f' g g' sq.w E ≫
              (schemeDerivedDirectImage f').map c) ≫ b.hom =
            a.hom ≫ T.map
              (schemeDerivedBaseChangeMap fA (pullback.snd fA gA) gA (pullback.fst fA gA)
                pullback.condition E ≫ (schemeDerivedDirectImage (pullback.snd fA gA)).map c0)
       := by
  sorry

end AlgebraicGeometry
