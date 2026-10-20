/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectHomComparisonTriangle

/-! # Projection comparison after cartesian transport -/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

omit [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] in
private theorem iso_triangle_cancel {C : Type*} [Category C]
    {P Q R S : C} (x : P ≅ Q) (y : Q ≅ R)
    (z : P ≅ S) (t : S ≅ R) (h : x ≪≫ y = z ≪≫ t) :
    y.hom ≫ t.inv ≫ z.inv = x.inv := by
  apply (cancel_epi x.hom).1
  have hh := congrArg Iso.hom h
  simp only [Iso.trans_hom] at hh
  simp only [← Category.assoc]
  rw [hh]
  simp only [Category.assoc, Category.id_comp, Iso.hom_inv_id]

/-- Composing a cartesian comparison with its first projection agrees with
pulling the first projection through base change. Source: Stacks Project,
Tag 0D5S. Replace the two named composite maps by their projection
factorizations. Apply the fixed three-arrow composition triangle to the
base-change map, the first projection, and the final arrow. Cancel its
forward and inverse factors; the remaining inverse component is the fixed
`perfectHomComparison`. -/
theorem perfectOverlapProjectionTailAbstract
    {W S Z : Scheme.{u}} (s : W ⟶ S)
    {T T' : Over S} (l : T' ⟶ T) (a : W ⟶ Z)
    (v : pullback s T'.hom ⟶ Z) (u : pullback s T.hom ⟶ Z)
    (hv : v = pullback.fst s T'.hom ≫ a)
    (hu : u = pullback.fst s T.hom ≫ a)
    (hm : baseChangeMap s l ≫ u = v)
    (M : schemeDerivedCategory Z) :
    (compositionTo (baseChangeMap s l) u v hm).hom.app M ≫
        (eqToIso (congrArg (fun k ↦ derivedPullback k) hv)).hom.app M ≫
          (perfectHomComposition (pullback.fst s T'.hom) a).inv.app M ≫
            (perfectHomComparison s l).hom.app ((derivedPullback a).obj M) =
      (derivedPullback (baseChangeMap s l)).map
        ((eqToIso (congrArg (fun k ↦ derivedPullback k) hu)).hom.app M) ≫
          (derivedPullback (baseChangeMap s l)).map
            ((perfectHomComposition (pullback.fst s T.hom) a).inv.app M) := by
  subst v
  subst u
  have htri := compositionTo_triangle (baseChangeMap s l)
    (pullback.fst s T.hom) a
    (pullback.fst s T.hom ≫ a)
    (pullback.fst s T'.hom ≫ a)
    (pullback.fst s T'.hom)
    rfl hm
    (baseChangeMap_fst s l) M
  have H := congrArg Iso.hom htri
  simp only [Iso.trans_hom, Functor.mapIso_hom] at H
  have hcomp := congrArg Iso.inv
    (perfectHomComparison_symm_eq_compositionTo s l
      ((derivedPullback a).obj M))
  simp only [Iso.symm_inv, Iso.app_hom] at hcomp
  have hc := iso_triangle_cancel
    ((derivedPullback (baseChangeMap s l)).mapIso
      ((compositionTo (pullback.fst s T.hom) a
        (pullback.fst s T.hom ≫ a) rfl).app M))
    ((compositionTo (baseChangeMap s l)
      (pullback.fst s T.hom ≫ a) (pullback.fst s T'.hom ≫ a) hm).app M)
    ((compositionTo (baseChangeMap s l) (pullback.fst s T.hom)
      (pullback.fst s T'.hom) (baseChangeMap_fst s l)).app
        ((derivedPullback a).obj M))
    ((compositionTo (pullback.fst s T'.hom) a
      (pullback.fst s T'.hom ≫ a) rfl).app M) htri
  simpa only [hcomp, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    (derivedPullback (baseChangeMap s l)).map_id,
    Category.id_comp, Category.comp_id, compositionTo,
    Iso.trans_inv, Iso.trans_hom, Iso.app_inv, Iso.app_hom,
    eqToIso_refl, Iso.trans_refl, Functor.mapIso_inv] using hc

end AlgebraicGeometry
