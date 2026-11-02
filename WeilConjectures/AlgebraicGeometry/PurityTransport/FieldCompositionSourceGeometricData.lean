/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportScalarLines

/-! # The geometric scalar comparisons in the source word

Source: scalar pullback and its monoidal normalization.
(blueprint: def-pur-field-composition-source-geometric-data). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Scheme
open CategoryTheory.Functor.OplaxMonoidal
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport
attribute [local irreducible] DerivedCategory Functor.leftDerivedFunctor
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

/-- The monoidal structure whose inverse tensorator is exactly scalarTensor.
It is constructed from the existing balanced ordinary tensorator and K-flat
left derivation; no map is selected by a bare existence of comparisons.
Source: scalar source coordinates
(blueprint: def-pur-field-composition-source-geometric-data). -/
@[instance_reducible] def fieldCompScalarMonoidal
    (ell : ℕ) [Fact ell.Prime] {c c' : Coefficient ell}
    (a : c.bundled.{u} ell ⟶ c'.bundled ell) (X : Scheme.{u}) :
    (scalarSixChange a X).Monoidal :=
  let φ := coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom X
  letI := (Mod.exists_extendScalarsMonoidal φ).choose
  letI := Mod.extendScalars_preservesFlat φ
  letI := (Mod.extendRestrictAdjunction φ).isLeftAdjoint
  (Mod.extendScalars φ).leftDerivedFunctorMonoidal

/-- The literal pullback factor of sourceScalar, including total-to-exact
comparison on both ends. Source: scalar source coordinates
(blueprint: def-pur-field-composition-source-geometric-data). -/
def fieldCompScalarPull
    (ell : ℕ) [Fact ell.Prime] {c c' : Coefficient ell}
    (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    actualPull (c.obj ell) f ⋙ scalarSixChange a X ≅
      scalarSixChange a Y ⋙ actualPull (c'.obj ell) f :=
  Functor.isoWhiskerRight
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory (c.obj ell) f) _ ≪≫
    scalarPullbackIso a f ≪≫
    (Functor.isoWhiskerLeft _
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory (c'.obj ell) f)).symm

end AlgebraicGeometry.ProEtale.PurityTransport
