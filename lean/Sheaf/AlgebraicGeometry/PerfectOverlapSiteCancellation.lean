/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreData
import Sheaf.AlgebraicGeometry.PerfectOverlapSiteCancellationAbstract

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian
  schemeOpenRestriction_additive schemeOpenRestriction_preservesFiniteLimits
  schemeOpenRestriction_preservesFiniteColimits

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (Z : Scheme.{u}) (U : Z.Opens),
  HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]

/-- The return map becomes the counit after moving back to the scheme site.
The defining composition comparison of `openSiteReturnIso` inserts the
equivalence unit; the triangle identity for the site equivalence cancels it. -/
theorem openSiteReturn_counit_app
    (X : Scheme.{u}) (W : X.Opens) (E : schemeDerivedCategory X) :
    let e : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W) ≌
      SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace) :=
      Scheme.Modules.overEquiv W
    let R := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W
    let PU := (schemeOpenRestriction X W).mapDerivedCategory
    e.mapDerivedCategory.functor.map ((openSiteReturnIso X W).hom.app E) ≫
      ((Functor.mapDerivedCategoryCompIso R e.functor).symm).hom.app E =
      e.mapDerivedCategory.counitIso.hom.app (PU.obj E) := by
  intro e R PU
  unfold openSiteReturnIso
  simp only [Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.rightUnitor_hom_app,
    Category.id_comp, Functor.map_comp, Category.assoc]
  exact equivalence_return_cancel e.mapDerivedCategory (R.mapDerivedCategory.obj E)
    (PU.obj E) ((Functor.mapDerivedCategoryCompIso R e.functor).app E)

/-- The apex equivalence maps the open-site return and composition maps to
the site counit on the overlap scheme. This is the component form used in
the canonical overlap object pin. -/
theorem perfectOverlapApex_siteReturn_comp
    {X Y S T : Scheme.{u}} (g : X ⟶ Y) (pX : X ⟶ T)
    (pY : Y ⟶ S) (b : T ⟶ S) (hg : IsPullback g pX pY b)
    (U V : Y.Opens) (E : schemeDerivedCategory X) :
    let W := g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V
    let e : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W) ≌
      SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace) :=
      Scheme.Modules.overEquiv W
    let Rw := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W
    let cart := perfectOverlapStageEquivalence g pX pY b hg U V
    (perfectOverlapApexEquivalence g pX pY b hg U V).functor.map
        ((openSiteReturnIso X W).hom.app E) ≫
      cart.functor.map ((Functor.mapDerivedCategoryCompIso Rw e.functor).symm.hom.app E) =
        cart.functor.map (e.mapDerivedCategory.counitIso.hom.app
          ((schemeOpenRestriction X W).mapDerivedCategory.obj E)) := by
  intro W e Rw cart
  have h := congrArg cart.functor.map (openSiteReturn_counit_app X W E)
  simp only [Functor.map_comp] at h
  exact h

end AlgebraicGeometry
