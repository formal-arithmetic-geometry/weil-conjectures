/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Geometry.RingedSpace.Basic

/-! # Stalks of the open-extension counit

Source: Stacks Project, Sheaves, Tag 00A7, clauses (2)--(4).
(blueprint: lem-sc-open-extension-counit-stalk)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace SheafOfModules

/-- The counit of any left adjoint to open restriction is an isomorphism on
stalks inside the open, and its source has zero stalks outside the open.
Source: Stacks Project, Sheaves, Tag 00A7, clauses (2)--(4).
(blueprint: lem-sc-open-extension-counit-stalk)

Proof: Construct extension by zero as the direct-sum extension presheaf followed
by module sheafification. Its stalk outside the open is zero: every neighborhood
of such a point has no morphism into the open, so its direct-sum extension value
is zero. Inside the
open its stalk agrees with the input stalk; restricting to neighborhoods contained
in the open is cofinal, and sheafification leaves stalks unchanged. For the
restriction of a global module, the counit on such neighborhoods evaluates to
the identity, hence induces an isomorphism on stalks. The adjunction uniqueness
isomorphism identifies any other left adjoint with this construction, compatibly
with the counits. Apply the underlying abelian stalk functor to that isomorphism
and transport the inside isomorphism and outside zero-object property. This uses
no covering hypothesis and includes both the empty and whole-space opens. -/
theorem open_extension_counit_stalk (X : AlgebraicGeometry.RingedSpace.{u})
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (_hR : R = (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)
    (W : Opens X)
    (S : SheafOfModules.{u} (R.over W) ⥤ SheafOfModules.{u} R)
    (a : S ⊣ overFunctor.{u} R W) (F : SheafOfModules.{u} R) (x : X) :
    let T := toSheaf R ⋙ TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
    (x ∈ W → IsIso (T.map (a.counit.app F))) ∧
      (x ∉ W → IsZero (T.obj (S.obj ((overFunctor.{u} R W).obj F)))) := by sorry

end SheafOfModules
