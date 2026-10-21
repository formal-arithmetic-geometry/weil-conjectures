/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectHomCompositionPrism
public import WeilConjectures.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreBase

/-! # Cartesian transport and the fixed composition prism -/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- The named cartesian transport is the middle face of the pullback
composition prism. Source: Stacks Project, Tag 0D5S.

Proof: Apply `compositionTo_prism` with the two cartesian isomorphism maps.
Its middle two factors are exactly the definition of the fixed transport;
associativity of isomorphism composition gives the displayed equation. -/
theorem perfectOverlapTransport_prism
    {X K A B Y : Scheme.{u}}
    (r : X ⟶ K) (eX : X ≅ A) (eK : K ≅ B) (m : A ⟶ B)
    (hmap : eX.inv ≫ r = m ≫ eK.inv)
    (p : K ⟶ Y) (q : X ⟶ Y) (hr : r ≫ p = q)
    (M : schemeDerivedCategory Y) :
    (derivedPullback eX.inv).mapIso ((compositionTo r p q hr).app M) ≪≫
        (compositionTo eX.inv q (eX.inv ≫ q) rfl).app M =
      (perfectOverlapDerivedPullbackTransport r eX eK m hmap).app
          ((derivedPullback p).obj M) ≪≫
        ((derivedPullback m).mapIso
            ((compositionTo eK.inv p (eK.inv ≫ p) rfl).app M) ≪≫
          (compositionTo m (eK.inv ≫ p) (eX.inv ≫ q)
            (by rw [← hr, ← Category.assoc, ← hmap, Category.assoc])).app M) := by
  have h := compositionTo_prism eX.inv r p m eK.inv q (eK.inv ≫ p)
    (eX.inv ≫ q) hr rfl rfl
    (by rw [← hr, ← Category.assoc, ← hmap, Category.assoc]) hmap M
  apply Iso.ext
  have hh := congrArg Iso.hom h
  simpa only [perfectOverlapDerivedPullbackTransport, compositionTo,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, NatTrans.comp_app,
    Functor.mapIso_hom, eqToIso_refl, Iso.trans_refl, Iso.app_inv,
    Iso.refl_hom, Category.comp_id,
    Category.assoc] using hh

end AlgebraicGeometry
