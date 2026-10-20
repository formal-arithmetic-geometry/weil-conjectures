/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectOverlapTransportPrismHom
public import Sheaf.AlgebraicGeometry.PerfectOverlapProjectionTailAbstract

/-! # Cartesian transport followed by projection -/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- The fixed cartesian comparison commutes with the first projection.
Source: Stacks Project, Tag 0D5S. Apply the cartesian pullback prism to the
restricted square, then apply the abstract projection triangle to its final
arrow. The cartesian equation and the restricted-square equation identify
the middle composite. -/
theorem perfectOverlapProjectionCompositeAbstract
    {X K W S Z : Scheme.{u}} (s : W ⟶ S)
    {T T' : Over S} (l : T' ⟶ T)
    (r : X ⟶ K) (eX : X ≅ pullback s T'.hom)
    (eK : K ≅ pullback s T.hom)
    (hmap : eX.inv ≫ r = baseChangeMap s l ≫ eK.inv)
    (p : K ⟶ Z) (t : X ⟶ Z) (hr : r ≫ p = t)
    (a : W ⟶ Z)
    (ht : eX.inv ≫ t = pullback.fst s T'.hom ≫ a)
    (hp : eK.inv ≫ p = pullback.fst s T.hom ≫ a)
    (M : schemeDerivedCategory Z) :
    (derivedPullback eX.inv).map ((compositionTo r p t hr).hom.app M) ≫
        (perfectHomComposition eX.inv t).hom.app M ≫
          (eqToIso (congrArg (fun k ↦ derivedPullback k) ht)).hom.app M ≫
            (perfectHomComposition (pullback.fst s T'.hom) a).inv.app M ≫
              (perfectHomComparison s l).hom.app ((derivedPullback a).obj M) =
      (perfectOverlapDerivedPullbackTransport r eX eK
        (baseChangeMap s l) hmap).hom.app ((derivedPullback p).obj M) ≫
        (derivedPullback (baseChangeMap s l)).map
          ((perfectHomComposition eK.inv p).hom.app M) ≫
          (derivedPullback (baseChangeMap s l)).map
            ((eqToIso (congrArg (fun k ↦ derivedPullback k) hp)).hom.app M) ≫
          (derivedPullback (baseChangeMap s l)).map
            ((perfectHomComposition (pullback.fst s T.hom) a).inv.app M) := by
  have hm : baseChangeMap s l ≫ (eK.inv ≫ p) = eX.inv ≫ t := by
    rw [← Category.assoc, ← hmap, Category.assoc, hr]
  have hpr := perfectOverlapTransport_prism_hom r eX eK
    (baseChangeMap s l) hmap p t hr M
  have htail := perfectOverlapProjectionTailAbstract s l a
    (eX.inv ≫ t) (eK.inv ≫ p) ht hp hm M
  rw [reassoc_of% hpr]
  rw [htail]

end AlgebraicGeometry
