/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedModuleBaseChangeMap

/-! # Transport of a module pullback comparison across a scheme isomorphism

Source: Stacks Project, Tags 06YJ, 08HY and 0D5S.
(blueprint: lem-pc-module-pullback-comparison-iso-transport).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- A comparison on a module transports through an isomorphism over its base.
Source: Stacks Project, Tag 06YJ, left-derived pullback; Tag 0D5S, composition;
Tag 08HY, counit construction.
(blueprint: lem-pc-module-pullback-comparison-iso-transport).

Proof: Direct image along e.hom is an exact equivalence, inverse to tensor
pullback along e.hom. Tensor pullback composition and e.hom followed by p = a
identify e_*(a^*G) with p^*G. The exact equivalence commutes with localization
and with the single functor; these identifications give m, independently of j.
Unpack hc as a left-derived counit epsilon. Postcompose epsilon with the exact
equivalence e_* and the underived composition identification. Postcomposition by
an equivalence preserves the right Kan extension universal property defining a
left-derived functor. Precompose this counit with j.inv to get a witnessing
left-derived counit for Lp^*. Its value at G[0], followed by the single-complex
identification, defines d. Naturality of the single-complex identifications
and j.hom followed by j.inv = identity give U(c) followed by m = j followed by d.
Thus every supplied j works: any automorphism in j is absorbed in the new
witnessing counit. No flatness of G is assumed. The exact-equivalence argument
also covers the zero module and the empty scheme. -/
theorem exists_modulePullbackComparison_iso_transport
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (a : Y ⟶ Z), (Scheme.Modules.tensorPullback a).Additive]
    {X Y P : Scheme.{u}} (a : Y ⟶ X) (p : P ⟶ X) (e : Y ≅ P)
    (hp : e.hom ≫ p = a)
    (j : derivedPullback a ⋙ schemeDerivedDirectImage e.hom ≅ derivedPullback p)
    (G : X.Modules)
    (c : (derivedPullback a).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback a).obj G))
    (hc : IsDerivedModulePullbackComparison a G c) :
    let E := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G
    let N := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings P.toRingedSpace)) 0).obj
        ((Scheme.Modules.tensorPullback p).obj G)
    ∃ d : (derivedPullback p).obj E ⟶ N,
      IsDerivedModulePullbackComparison p G d ∧
      ∃ m : (schemeDerivedDirectImage e.hom).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              ((Scheme.Modules.tensorPullback a).obj G)) ≅ N,
        (schemeDerivedDirectImage e.hom).map c ≫ m.hom = j.hom.app E ≫ d := by sorry

end AlgebraicGeometry
