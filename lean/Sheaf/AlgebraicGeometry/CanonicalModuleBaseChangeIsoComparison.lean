/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedModuleBaseChangeMap

import Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
import Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap

/-! # Canonical module base change under changes of coordinates

Source: Stacks Project, Tags 08HY, 0D5T, and 08IB.
(blueprint: lem-pc-canonical-module-base-change-iso-comparison).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry

/-- Changing the two base coordinates by isomorphisms preserves the canonical
module base-change arrow. This statement involves no open restriction.
Source: Stacks Project, Tag 08HY, counit construction; Tag 0D5T, composition;
Tag 08IB, affine coordinate change in the first proof paragraph.
(blueprint: lem-pc-canonical-module-base-change-iso-comparison).

Proof:
1. The isomorphisms eS and eT identify the original cartesian square with the
chosen pullback of f followed by eS.hom and eT.inv followed by g and eS.hom.
The unique pullback isomorphism preserves the first projection and takes the
second projection, followed by eT.inv, to f'.
2. Pullback along a scheme isomorphism is an exact equivalence on modules.
Its derived functor is the induced equivalence on derived categories. Direct
image along the inverse is its inverse equivalence. Apply composition of derived
pullbacks and direct images and the inverse-coordinate identities to obtain a.
Use the pullback isomorphism and tensor-pullback composition to identify the
ordinary pulled-back modules; derive this identification and then apply direct
image composition to obtain b.
3. Transport the witnessing counit in hc through the pullback isomorphism.
Composition with exact equivalences preserves its left-derived universal
property. Evaluating on G[0] and inserting the ordinary tensor-pullback
identification gives c0 with the required comparison predicate.
4. Transpose both base-change mates under the adjunction for the second
projection. The pullback composition comparisons identify their transposes:
both are pullback of the same counit of f, with inverse coordinates cancelled.
Injectivity of the adjunction Hom equivalence gives the equality of mates.
Naturality then composes with the transported module counit from step 3,
giving the displayed square. This also applies to empty schemes and zero modules. -/
theorem exists_canonicalModuleBaseChange_iso_comparison
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
    {A B : Scheme.{u}} (eS : S ≅ A) (eT : S' ≅ B) :
    let fA := f ≫ eS.hom
    let gA := eT.inv ≫ g ≫ eS.hom
    let E := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G
    let T := schemeDerivedDirectImage eT.inv
    ∃ c0 : (derivedPullback (pullback.fst fA gA)).obj E ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings (pullback fA gA).toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback (pullback.fst fA gA)).obj G),
      IsDerivedModulePullbackComparison (pullback.fst fA gA) G c0 ∧
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
      := by sorry

end AlgebraicGeometry
