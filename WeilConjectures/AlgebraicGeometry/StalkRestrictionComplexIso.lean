/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.AlgebraicGeometry.Stalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Canonical comparison of restriction followed by stalk pullback

For an open `V` containing `y`, restricting a complex of modules to `V` and then pulling back
to `Spec 𝒪_{Y,y}` is canonically isomorphic to pulling back along `Y.fromSpecStalk y`.

## Implementation details

The comparison replaces restriction by pullback along the open inclusion
(`restrictFunctorIsoPullback`), composes the pullbacks (`pullbackComp`) and uses
`Opens.fromSpecStalkOfMem_ι`; it is then applied termwise to complexes.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical isomorphism, on complexes, between restriction to `V` followed by pullback
along `V.fromSpecStalkOfMem y hyV` and pullback along `Y.fromSpecStalk y`. -/
noncomputable def stalkRestrictionComplexIso {Y : Scheme.{u}} (V : Y.Opens)
    (y : Y) (hyV : y ∈ V) :
    (restrictFunctor V.ι).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      (Modules.pullback (V.fromSpecStalkOfMem y hyV)).mapHomologicalComplex
        (ComplexShape.up ℤ) ≅
      (Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex (ComplexShape.up ℤ) :=
  Functor.mapHomologicalComplexCompIso
    (Functor.isoWhiskerRight (restrictFunctorIsoPullback V.ι)
        (Modules.pullback (V.fromSpecStalkOfMem y hyV)) ≪≫
      pullbackComp (V.fromSpecStalkOfMem y hyV) V.ι ≪≫
      pullbackCongr (V.fromSpecStalkOfMem_ι y hyV)) (ComplexShape.up ℤ)

end AlgebraicGeometry.Scheme.Modules
