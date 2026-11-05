/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedToposMorphism

/-!
# The ring data of a ringed geometric morphism

The geometric adjunction and its structural ring map, before constructing the induced
module direct image. Source: Stacks Project, Modules on Sites, ringed topoi and
pushforward of modules.
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- The geometric adjunction and structural ring map of `RingedToposMorphism`.
This contains no choice of a module direct image. -/
structure RingedToposMorphism.RingData
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J RingCat.{u}) (B : Sheaf K RingCat.{u}) where
  /-- Inverse image of sheaves of sets. -/
  inverse : Sheaf K (Type u) ⥤ Sheaf J (Type u)
  /-- Direct image of sheaves of sets. -/
  direct : Sheaf J (Type u) ⥤ Sheaf K (Type u)
  /-- The geometric adjunction. -/
  adj : inverse ⊣ direct
  /-- Left exactness is required only for the underlying inverse image. -/
  leftExact : PreservesFiniteLimits inverse
  /-- The structural map, with ring structure specified by generalized elements below. -/
  ringMap : inverse.obj ((sheafCompose K (forget RingCat)).obj B) ⟶
    (sheafCompose J (forget RingCat)).obj A
  /-- Preservation of zero. -/
  ring_zero : ∀ (T : Sheaf K (Type u))
    (z : T ⟶ (sheafCompose K (forget RingCat)).obj B),
    (∀ (U : Dᵒᵖ) (t : T.obj.obj U),
      z.hom.app U t = @Zero.zero (B.obj.obj U) inferInstance) →
    ∀ (U : Cᵒᵖ) (t : (inverse.obj T).obj.obj U),
      ((inverse.map z) ≫ ringMap).hom.app U t = @Zero.zero (A.obj.obj U) inferInstance
  /-- Preservation of one. -/
  ring_one : ∀ (T : Sheaf K (Type u))
    (z : T ⟶ (sheafCompose K (forget RingCat)).obj B),
    (∀ (U : Dᵒᵖ) (t : T.obj.obj U),
      z.hom.app U t = @One.one (B.obj.obj U) inferInstance) →
    ∀ (U : Cᵒᵖ) (t : (inverse.obj T).obj.obj U),
      ((inverse.map z) ≫ ringMap).hom.app U t = @One.one (A.obj.obj U) inferInstance
  /-- Preservation of add. -/
  ring_add : ∀ (T : Sheaf K (Type u))
    (x y z : T ⟶ (sheafCompose K (forget RingCat)).obj B),
    (∀ (U : Dᵒᵖ) (t : T.obj.obj U),
      z.hom.app U t = @Add.add (B.obj.obj U) inferInstance (x.hom.app U t) (y.hom.app U t)) →
    ∀ (U : Cᵒᵖ) (t : (inverse.obj T).obj.obj U),
      ((inverse.map z) ≫ ringMap).hom.app U t =
        @Add.add (A.obj.obj U) inferInstance
          (((inverse.map x) ≫ ringMap).hom.app U t)
          (((inverse.map y) ≫ ringMap).hom.app U t)
  /-- Preservation of mul. -/
  ring_mul : ∀ (T : Sheaf K (Type u))
    (x y z : T ⟶ (sheafCompose K (forget RingCat)).obj B),
    (∀ (U : Dᵒᵖ) (t : T.obj.obj U),
      z.hom.app U t = @Mul.mul (B.obj.obj U) inferInstance (x.hom.app U t) (y.hom.app U t)) →
    ∀ (U : Cᵒᵖ) (t : (inverse.obj T).obj.obj U),
      ((inverse.map z) ≫ ringMap).hom.app U t =
        @Mul.mul (A.obj.obj U) inferInstance
          (((inverse.map x) ≫ ringMap).hom.app U t)
          (((inverse.map y) ≫ ringMap).hom.app U t)

namespace RingedToposMorphism.RingData

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {A : Sheaf J RingCat.{u}} {B : Sheaf K RingCat.{u}}

local instance (U : Dᵒᵖ) :
    Ring (((sheafCompose K (forget RingCat)).obj B).obj.obj U) :=
  inferInstanceAs (Ring (B.obj.obj U))

local instance (U : Cᵒᵖ) :
    Ring (((sheafCompose J (forget RingCat)).obj A).obj.obj U) :=
  inferInstanceAs (Ring (A.obj.obj U))

variable (g : RingedToposMorphism.RingData A B)

/-- A lift of the direct image to modules, with the structural-map-induced action. -/
structure Modules (d : RingedToposMorphism.RingData A B) where
  /-- The induced direct image on module sheaves. -/
  modules : SheafOfModules.{u} A ⥤ SheafOfModules.{u} B
  /-- Additivity of the induced direct image. -/
  additive : modules.Additive
  /-- The underlying direct image of sheaves of sets, naturally in the module. -/
  underlying :
    modules ⋙ SheafOfModules.toSheaf B ⋙ sheafCompose K (forget AddCommGrpCat) ≅
      (SheafOfModules.toSheaf A ⋙ sheafCompose J (forget AddCommGrpCat)) ⋙ d.direct
  /-- Addition and the structural-map-induced scalar action, under adjunction. -/
  module_linear : ∀ (M : SheafOfModules.{u} A) (T : Sheaf K (Type u))
    (a : T ⟶ (sheafCompose K (forget RingCat)).obj B)
    (x y z : T ⟶ (sheafCompose K (forget AddCommGrpCat)).obj
      ((SheafOfModules.toSheaf B).obj (modules.obj M))),
    (∀ (U : Dᵒᵖ) (t : T.obj.obj U),
      z.hom.app U t = @Add.add ((modules.obj M).val.obj U) inferInstance
        (@SMul.smul (B.obj.obj U) ((modules.obj M).val.obj U) inferInstance
          (a.hom.app U t) (x.hom.app U t)) (y.hom.app U t)) →
    ∀ (U : Cᵒᵖ) (t : (d.inverse.obj T).obj.obj U),
      ((d.adj.homEquiv T _).symm (z ≫ underlying.hom.app M)).hom.app U t =
        @Add.add (M.val.obj U) inferInstance
          (@SMul.smul (A.obj.obj U) (M.val.obj U) inferInstance
            (((d.inverse.map a) ≫ d.ringMap).hom.app U t)
            (((d.adj.homEquiv T _).symm (x ≫ underlying.hom.app M)).hom.app U t))
          (((d.adj.homEquiv T _).symm (y ≫ underlying.hom.app M)).hom.app U t)

end RingedToposMorphism.RingData
end CategoryTheory

namespace CategoryTheory.RingedToposMorphism.RingData

section

open CategoryTheory CategoryTheory.Limits
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {A : Sheaf J RingCat.{u}} {B : Sheaf K RingCat.{u}}
variable (g : RingedToposMorphism.RingData A B)

/-- Assemble geometric ring data and its induced module direct image. -/
def withModules (d : RingedToposMorphism.RingData A B) (m : d.Modules) :
    RingedToposMorphism A B where
  inverse := d.inverse
  direct := d.direct
  adj := d.adj
  leftExact := d.leftExact
  ringMap := d.ringMap
  ring_zero := d.ring_zero
  ring_one := d.ring_one
  ring_add := d.ring_add
  ring_mul := d.ring_mul
  modules := m.modules
  additive := m.additive
  underlying := m.underlying
  module_linear := m.module_linear

end

end CategoryTheory.RingedToposMorphism.RingData
