/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidalComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPullMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.CompMonoidal

/-!
# The underived (Pull) isomorphism is monoidal

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings and `f : X ⟶ Y` a morphism of
schemes. The underived (Pull) isomorphism
`ProEtale.CondensedRing.pullIso a f : f^*_Λ ⋙ Ext_{a_X} ≅ Ext_{a_Y} ⋙ f^*_Λ'` is a monoidal
natural isomorphism (`ProEtale.CondensedRing.isMonoidal_pullIso_hom`), for the strong monoidal
structures of the pullbacks (`ProEtale.CondensedRing.monoidal_upperStar`) and of the extensions
of scalars (`Mod.extendScalarsMonoidal`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The underived (Pull) isomorphism is monoidal**: `pullIso a f` commutes with the tensor
comparisons of the composite strong monoidal functors `f^*_Λ ⋙ Ext_{a_X}` and
`Ext_{a_Y} ⋙ f^*_Λ'`. -/
theorem isMonoidal_pullIso_hom :
    letI := Mod.extendScalarsMonoidal (coefficientMap a X)
    letI := Mod.extendScalarsMonoidal (coefficientMap a Y)
    NatTrans.IsMonoidal (pullIso a f).hom := sorry

end AlgebraicGeometry.ProEtale.CondensedRing
