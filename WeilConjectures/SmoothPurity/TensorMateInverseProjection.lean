/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula

/-! # The coefficient-first inverse projection under etale precomposition

Source: blueprint `thm-asd-smooth-tensor.proof.md`, paragraph 3, expanded in steps 1 and 3
of lem-asd-tensor-mate-etale-precomp.
-/

@[expose] public section

set_option autoImplicit false

universe v

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Etale

/-- The coefficient-first inverse compact-support projection, natural in the source object.
Source: Stacks Tag 0GL5; the two signed symmetries and the exact-pullback comparison only
change the order and the presentation of its factors.
(blueprint: def-asd-tensor-mate-inverse-projection). -/
noncomputable def tensorMateInverseProjection
    (A : Type (v + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{v}} (f : X ⟶ S) [HasCompactification f]
    (K : DerivedCategoryModule A S) :
    (derivedTensor (ModuleCat A) X).obj ((f)^*[ModuleCat A].mapDerivedCategory.obj K) ⋙
        R(f)_![ModuleCat A] ⟶
      R(f)_![ModuleCat A] ⋙ (derivedTensor (ModuleCat A) S).obj K :=
  let F := R(f)_![ModuleCat A]
  let T := derivedTensor (ModuleCat A) X
  let l := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat A) f
  let p := @inv _ _ _ _ (projectionMap (ModuleCat A) f)
    (isIso_projectionMap_of_finite A f)
  Functor.whiskerRight (T.map (l.inv.app K)) F ≫
    Functor.whiskerRight ((derivedTensorSymmetry (ModuleCat A) X).hom.app
      ((f)^*[ModuleCat A].leftDerivedFunctor.obj K)) F ≫
    Functor.whiskerRight p ((evaluation _ _).obj K) ≫
    Functor.whiskerLeft F (((flipFunctor _ _ _).map
      (derivedTensorSymmetry (ModuleCat A) S).hom).app K)

end AlgebraicGeometry.Etale
