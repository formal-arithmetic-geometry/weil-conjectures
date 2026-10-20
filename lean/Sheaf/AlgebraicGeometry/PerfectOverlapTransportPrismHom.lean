/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectOverlapTransportPrism

/-! # Component form of the fixed cartesian pullback prism -/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- The hom component of the fixed cartesian prism, with its identity
transports removed. Source: Stacks Project, Tag 0D5S. Apply `Iso.hom` to the
fixed prism, expand composition of isomorphisms, and remove the two reflexive
equality transports. -/
theorem perfectOverlapTransport_prism_hom
    {X K A B Y : Scheme.{u}}
    (r : X ⟶ K) (eX : X ≅ A) (eK : K ≅ B) (m : A ⟶ B)
    (hmap : eX.inv ≫ r = m ≫ eK.inv)
    (p : K ⟶ Y) (q : X ⟶ Y) (hr : r ≫ p = q)
    (M : schemeDerivedCategory Y) :
    (derivedPullback eX.inv).map ((compositionTo r p q hr).hom.app M) ≫
      (perfectHomComposition eX.inv q).hom.app M =
    (perfectOverlapDerivedPullbackTransport r eX eK m hmap).hom.app
        ((derivedPullback p).obj M) ≫
      (derivedPullback m).map ((perfectHomComposition eK.inv p).hom.app M) ≫
        (compositionTo m (eK.inv ≫ p) (eX.inv ≫ q)
          (by rw [← hr, ← Category.assoc, ← hmap, Category.assoc])).hom.app M := by
  have H := congrArg Iso.hom
    (perfectOverlapTransport_prism r eX eK m hmap p q hr M)
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    compositionTo, eqToIso_refl, Iso.trans_refl,
    NatTrans.comp_app, Category.assoc] using H

end AlgebraicGeometry
