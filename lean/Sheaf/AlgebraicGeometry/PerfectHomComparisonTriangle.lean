/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectHomComparisonTriangle
public import WeilConjectures.AlgebraicGeometry.PerfectHomTransportExtension
import all WeilConjectures.AlgebraicGeometry.PerfectHomTransportExtension

/-! # Public composition helpers for projection triangles

The adopted source supplies `perfectHomComparison_triangle`. Its composition helpers
are private, so this module retains the public helpers used by the prism and
projection-tail arguments.

Source: Stacks Project, Tag 0D5S, composition of derived pullbacks.
(blueprint: lem-pc-perfect-hom-comparison-triangle). -/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] perfectHomComposition

variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- The fixed derived-pullback comparison transported along an equality of scheme maps. -/
noncomputable def compositionTo {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (p : Y ⟶ Z) (q : X ⟶ Z) (e : f ≫ p = q) :
    derivedPullback p ⋙ derivedPullback f ≅ derivedPullback q :=
  perfectHomComposition f p ≪≫ eqToIso (congrArg (fun k ↦ derivedPullback k) e)

/-- The three-arrow triangle for the fixed derived-pullback comparisons. -/
theorem compositionTo_triangle {W X Y Z : Scheme.{u}}
    (h : W ⟶ X) (f : X ⟶ Y) (p : Y ⟶ Z)
    (q : X ⟶ Z) (r : W ⟶ Z) (t : W ⟶ Y)
    (eq : f ≫ p = q) (er : h ≫ q = r) (et : h ≫ f = t)
    (P : schemeDerivedCategory Z) :
    (derivedPullback h).mapIso ((compositionTo f p q eq).app P) ≪≫
      (compositionTo h q r er).app P =
    (compositionTo h f t et).app ((derivedPullback p).obj P) ≪≫
      (compositionTo t p r (by rw [← et, Category.assoc, eq, er])).app P := by
  subst q
  subst r
  subst t
  have hh := congrArg (fun α ↦ α.hom.app P) (cc_assoc h f p)
  apply Iso.ext
  simp only [compositionTo, Iso.trans_hom, NatTrans.comp_app,
    Functor.mapIso_hom, Iso.app_hom, eqToIso_refl, Iso.refl_hom,
    Category.comp_id, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Category.id_comp] at hh ⊢
  exact hh

private theorem comparison_symm {X S : Scheme.{u}} (s : X ⟶ S)
    {T T' : Over S} (g : T' ⟶ T) (P : schemeDerivedCategory X) :
    ((perfectHomComparison s g).app P).symm =
      (compositionTo (baseChangeMap s g) (pullback.fst s T.hom)
        (pullback.fst s T'.hom) (baseChangeMap_fst s g)).app P := by
  apply Iso.ext
  simp only [perfectHomComparison, compositionTo, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, NatTrans.comp_app,
    eqToIso.hom, eqToIso.inv]

/-- The inverse fixed base-change comparison is the pullback-composition
comparison for its first projection. Source: Stacks Project, Tag 0D5S.

Proof: Expand the definition of `perfectHomComparison` and invert its two
factors. The projection equality is exactly `baseChangeMap_fst`. -/
theorem perfectHomComparison_symm_eq_compositionTo
    {X S : Scheme.{u}} (s : X ⟶ S) {T T' : Over S} (g : T' ⟶ T)
    (P : schemeDerivedCategory X) :
    ((perfectHomComparison s g).app P).symm =
      (compositionTo (baseChangeMap s g) (pullback.fst s T.hom)
        (pullback.fst s T'.hom) (baseChangeMap_fst s g)).app P :=
  comparison_symm s g P

end AlgebraicGeometry
