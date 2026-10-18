/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Ring and module inverse images at a topos point

Source: Stacks Project, Sites, Proposition 00YV; Modules on Sites, Section 03D2;
Cohomology on Sites, Tag 0DEN (blueprint: def-sfb-ringed-site-point).

The operation graphs are tested on every sheaf T, including the products of operand
sheaves. They specify the finite-product transport, rather than an arbitrary lift.
No object is selected from an existence theorem: all data remain explicit in the
presentation, and the criterion will hold for every such presentation.
-/

@[expose] public section
set_option autoImplicit false

universe u v w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- A presentation of the ring and module stalks at a point, with their induced
operations. The natural underlying-set isomorphism fixes the maps as well as the
objects. Testing operation graphs on product sheaves specifies exactly transport
by the inverse finite-product comparison; constants use the terminal sheaf.
Source: Stacks 00YV and 03D2 (blueprint: def-sfb-ringed-site-point). -/
structure RingedSitePoint
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w})
    (p : GeometricMorphism (Type w) (Sheaf J (Type w))) where
  ring : CommRingCat.{w}
  ringUnderlying : p.inverse.obj ((sheafCompose J (forget CommRingCat.{w})).obj R) ≅
    (forget CommRingCat.{w}).obj ring
  ringAdd : ∀ (T : Sheaf J (Type w))
    (a b t : T ⟶ ((sheafCompose J (forget CommRingCat.{w})).obj R)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U),
      (@id (R.obj.obj U) (t.hom.app U x)) =
        (@id (R.obj.obj U) (a.hom.app U x)) + (@id (R.obj.obj U) (b.hom.app U x))) →
    ∀ x : p.inverse.obj T,
      (@id ring (ringUnderlying.hom (p.inverse.map t x))) =
        (@id ring (ringUnderlying.hom (p.inverse.map a x))) +
          (@id ring (ringUnderlying.hom (p.inverse.map b x)))
  ringMul : ∀ (T : Sheaf J (Type w))
    (a b t : T ⟶ ((sheafCompose J (forget CommRingCat.{w})).obj R)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U),
      (@id (R.obj.obj U) (t.hom.app U x)) =
        (@id (R.obj.obj U) (a.hom.app U x)) * (@id (R.obj.obj U) (b.hom.app U x))) →
    ∀ x : p.inverse.obj T,
      (@id ring (ringUnderlying.hom (p.inverse.map t x))) =
        (@id ring (ringUnderlying.hom (p.inverse.map a x))) *
          (@id ring (ringUnderlying.hom (p.inverse.map b x)))
  ringZero : ∀ (T : Sheaf J (Type w)) (a : T ⟶ ((sheafCompose J (forget CommRingCat.{w})).obj R)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U), (@id (R.obj.obj U) (a.hom.app U x)) = 0) →
    ∀ x : p.inverse.obj T,
      (@id ring (ringUnderlying.hom (p.inverse.map a x))) = 0
  ringOne : ∀ (T : Sheaf J (Type w)) (a : T ⟶ ((sheafCompose J (forget CommRingCat.{w})).obj R)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U), (@id (R.obj.obj U) (a.hom.app U x)) = 1) →
    ∀ x : p.inverse.obj T,
      (@id ring (ringUnderlying.hom (p.inverse.map a x))) = 1
  modules : ringedSiteModules.{w} ((sheafCompose J
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⥤ ModuleCat.{w} ring
  moduleUnderlying : modules ⋙ forget (ModuleCat.{w} ring) ≅
    (SheafOfModules.toSheaf _ ⋙ sheafCompose J (forget AddCommGrpCat.{w})) ⋙ p.inverse
  moduleAdd : ∀ (M : ringedSiteModules.{w} ((sheafCompose J
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
    (T : Sheaf J (Type w)) (a b t : T ⟶ ((SheafOfModules.toSheaf _ ⋙ sheafCompose J
      (forget AddCommGrpCat.{w})).obj M)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U),
      (@id (M.val.obj U) (t.hom.app U x)) =
        (@id (M.val.obj U) (a.hom.app U x)) + (@id (M.val.obj U) (b.hom.app U x))) →
    ∀ x : p.inverse.obj T,
      (@id (modules.obj M) ((moduleUnderlying.inv.app M) (p.inverse.map t x))) =
        (@id (modules.obj M) ((moduleUnderlying.inv.app M) (p.inverse.map a x))) +
          (@id (modules.obj M) ((moduleUnderlying.inv.app M) (p.inverse.map b x)))
  moduleZero : ∀ (M : ringedSiteModules.{w} ((sheafCompose J
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
    (T : Sheaf J (Type w)) (a : T ⟶ ((SheafOfModules.toSheaf _ ⋙ sheafCompose J
      (forget AddCommGrpCat.{w})).obj M)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U), (@id (M.val.obj U) (a.hom.app U x)) = 0) →
    ∀ x : p.inverse.obj T,
      (@id (modules.obj M) ((moduleUnderlying.inv.app M) (p.inverse.map a x))) = 0
  moduleSMul : ∀ (M : ringedSiteModules.{w} ((sheafCompose J
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
    (T : Sheaf J (Type w)) (a : T ⟶ ((sheafCompose J (forget CommRingCat.{w})).obj R))
    (b t : T ⟶ ((SheafOfModules.toSheaf _ ⋙ sheafCompose J
      (forget AddCommGrpCat.{w})).obj M)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U),
      (@id (M.val.obj U) (t.hom.app U x)) =
        (@id (R.obj.obj U) (a.hom.app U x)) • (@id (M.val.obj U) (b.hom.app U x))) →
    ∀ x : p.inverse.obj T,
      (@id (modules.obj M) ((moduleUnderlying.inv.app M) (p.inverse.map t x))) =
        (@id ring (ringUnderlying.hom (p.inverse.map a x))) •
          (@id (modules.obj M) ((moduleUnderlying.inv.app M) (p.inverse.map b x)))
  modules_additive : modules.Additive

attribute [instance] RingedSitePoint.modules_additive

/-- The finite-product transport has a normalized presentation at every point.
Source: Stacks 00YV, 03D2 (blueprint: def-sfb-ringed-site-point).

Proof: use the inverse binary-product and terminal comparisons of p.inverse to
transport the ring operations, and the addition and scalar action of every module.
Apply p.inverse to each algebraic identity and cancel its finite-product comparison;
this proves the ring and module axioms. Naturality makes the inverse image of a
module map linear and gives the natural underlying-set isomorphism. Addition of
module maps is addition followed by the diagonal pairing, so its transport also
proves additivity. The same calculation for arbitrary generalized sections gives
all the displayed operation-graph equations. No choice of unrelated ring or module
structures is involved: their operations are prescribed by these formulas. -/
theorem RingedSitePoint.nonempty
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w})
    (p : GeometricMorphism (Type w) (Sheaf J (Type w))) :
    Nonempty (RingedSitePoint R p) := by
  sorry

end CategoryTheory
