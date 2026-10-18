/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.CategoryTheory.RingedToposRingData

/-!
# Lifting the structural ring map in a geometric square

Source: Stacks Project, Modules on Sites, Tag 03CR, transport of the structural map.
(blueprint: lem-weil-pbc-ringed-topos-ring-square).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.RingedToposMorphism.RingData

variable {C D C' D' : Type u}
  [SmallCategory C] [SmallCategory D] [SmallCategory C'] [SmallCategory D']
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {J' : GrothendieckTopology C'} {K' : GrothendieckTopology D'}
  {A : Sheaf J RingCat.{u}} {B : Sheaf K RingCat.{u}}
  {A' : Sheaf J' RingCat.{u}} {B' : Sheaf K' RingCat.{u}}
  (f : RingedToposMorphism.RingData A B)
  (g : RingedToposMorphism.RingData A A')
  (e : RingedToposMorphism.RingData B B')
  (H : Sheaf K' (Type u) ⥤ Sheaf J' (Type u))
  [g.inverse.Full] [g.inverse.Faithful] [IsIso g.ringMap]
  (α : e.inverse ⋙ f.inverse ≅ H ⋙ g.inverse)

/-- The unique lift of the structural map through the fully faithful inverse image. -/
noncomputable def squareRingMap :
    H.obj ((sheafCompose K' (forget RingCat)).obj B') ⟶
      (sheafCompose J' (forget RingCat)).obj A' :=
  g.inverse.preimage
    (α.inv.app _ ≫ f.inverse.map e.ringMap ≫ f.ringMap ≫ inv g.ringMap)

omit [g.inverse.Faithful] in
/-- The lifted map intertwines all generalized elements of the square. -/
theorem squareRingMap_naturality (T : Sheaf K' (Type u))
    (x : T ⟶ (sheafCompose K' (forget RingCat)).obj B') :
    g.inverse.map (H.map x ≫ squareRingMap f g e H α) ≫ g.ringMap =
      α.inv.app T ≫ f.inverse.map (e.inverse.map x ≫ e.ringMap) ≫ f.ringMap := by
  simp only [Functor.map_comp, squareRingMap, Functor.map_preimage, Category.assoc]
  have hn : g.inverse.map (H.map x) ≫ α.inv.app _ =
      α.inv.app T ≫ f.inverse.map (e.inverse.map x) := α.inv.naturality x
  rw [← Category.assoc, ← Category.assoc, hn]
  simp

/-- The geometric bottom arrow with its lifted structural ring map.

The four ring identities are reflected by the faithful inverse image of the left
vertical equivalence, after checking them using the top and right arrows. -/
noncomputable def square
    (R : Sheaf J' (Type u) ⥤ Sheaf K' (Type u))
    (adjH : H ⊣ R) (hH : PreservesFiniteLimits H) :
    RingedToposMorphism.RingData A' B' where
  inverse := H
  direct := R
  adj := adjH
  leftExact := hH
  ringMap := squareRingMap f g e H α
  ring_zero T z hz := by
    apply g.reflect_zero (H.map z ≫ squareRingMap f g e H α)
    intro U t
    rw [squareRingMap_naturality]
    exact f.ring_zero (e.inverse.obj T) (e.inverse.map z ≫ e.ringMap)
      (e.ring_zero T z hz) U ((α.inv.app T).hom.app U t)
  ring_one T z hz := by
    apply g.reflect_one (H.map z ≫ squareRingMap f g e H α)
    intro U t
    rw [squareRingMap_naturality]
    exact f.ring_one (e.inverse.obj T) (e.inverse.map z ≫ e.ringMap)
      (e.ring_one T z hz) U ((α.inv.app T).hom.app U t)
  ring_add T x y z hz := by
    apply g.reflect_add (H.map x ≫ squareRingMap f g e H α)
      (H.map y ≫ squareRingMap f g e H α) (H.map z ≫ squareRingMap f g e H α)
    intro U t
    simp only [squareRingMap_naturality]
    exact f.ring_add (e.inverse.obj T) (e.inverse.map x ≫ e.ringMap)
      (e.inverse.map y ≫ e.ringMap) (e.inverse.map z ≫ e.ringMap)
      (e.ring_add T x y z hz) U ((α.inv.app T).hom.app U t)
  ring_mul T x y z hz := by
    apply g.reflect_mul (H.map x ≫ squareRingMap f g e H α)
      (H.map y ≫ squareRingMap f g e H α) (H.map z ≫ squareRingMap f g e H α)
    intro U t
    simp only [squareRingMap_naturality]
    exact f.ring_mul (e.inverse.obj T) (e.inverse.map x ≫ e.ringMap)
      (e.inverse.map y ≫ e.ringMap) (e.inverse.map z ≫ e.ringMap)
      (e.ring_mul T x y z hz) U ((α.inv.app T).hom.app U t)

omit [g.inverse.Faithful] in
/-- The square commutes with the lifted structural ring map. -/
theorem square_comm :
    f.inverse.map e.ringMap ≫ f.ringMap =
      α.hom.app ((sheafCompose K' (forget RingCat)).obj B') ≫
        g.inverse.map (squareRingMap f g e H α) ≫ g.ringMap := by
  simp only [squareRingMap, Functor.map_preimage, Category.assoc]
  simp

end CategoryTheory.RingedToposMorphism.RingData
