/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectOverlapRestrictedComposition

/-! # Component equations for the pinned open square -/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- Forward component of the pinned open-pullback square, expressed with the
fixed composition comparisons. Source: Stacks Project, Tag 0D5S.
Proof: Expand the four factors of the defining natural isomorphism. The two
composition factors are `compositionTo` for the square and its lower edge. -/
theorem singleComplexOpenPullbackSquareIso_hom_app_eq_compositionTo
    {X Y : Scheme.{u}} (s : X ⟶ Y) (U : Y.Opens) (U' : X.Opens)
    (j : U'.toScheme ⟶ U.toScheme) (hj : j ≫ U.ι = U'.ι ≫ s)
    (M : schemeDerivedCategory Y) :
    (singleComplexOpenPullbackSquareIso s U U' j hj).hom.app M =
      (derivedPullback j).map ((singleComplexOpenPullbackIso Y U).inv.app M) ≫
        (compositionTo j U.ι (U'.ι ≫ s) hj).hom.app M ≫
          (compositionTo U'.ι s (U'.ι ≫ s) rfl).inv.app M ≫
            (singleComplexOpenPullbackIso X U').hom.app
              ((derivedPullback s).obj M) := by
  simp only [singleComplexOpenPullbackSquareIso, NatIso.ofComponents_hom_app,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom,
    compositionTo, Iso.trans_inv, eqToIso.hom, eqToIso.inv,
    eqToHom_app, eqToHom_refl, NatTrans.comp_app, NatTrans.id_app,
    Category.id_comp, Category.comp_id, Category.assoc,
    singleComplexOpenPinnedComposition, perfectHomComposition]

/-- Inverse component of the same square, with the factors in reverse order.
Source: Stacks Project, Tag 0D5S. Invert the preceding component equation
and use functoriality of mapped isomorphisms. -/
theorem singleComplexOpenPullbackSquareIso_inv_app_eq_compositionTo
    {X Y : Scheme.{u}} (s : X ⟶ Y) (U : Y.Opens) (U' : X.Opens)
    (j : U'.toScheme ⟶ U.toScheme) (hj : j ≫ U.ι = U'.ι ≫ s)
    (M : schemeDerivedCategory Y) :
    (singleComplexOpenPullbackSquareIso s U U' j hj).inv.app M =
      (singleComplexOpenPullbackIso X U').inv.app ((derivedPullback s).obj M) ≫
        (compositionTo U'.ι s (U'.ι ≫ s) rfl).hom.app M ≫
          (compositionTo j U.ι (U'.ι ≫ s) hj).inv.app M ≫
            (derivedPullback j).map ((singleComplexOpenPullbackIso Y U).hom.app M) := by
  have h := congrArg Iso.inv
    (show (singleComplexOpenPullbackSquareIso s U U' j hj).app M =
      ((derivedPullback j).mapIso ((singleComplexOpenPullbackIso Y U).symm.app M) ≪≫
        (compositionTo j U.ι (U'.ι ≫ s) hj).app M ≪≫
          (compositionTo U'.ι s (U'.ι ≫ s) rfl).symm.app M ≪≫
            (singleComplexOpenPullbackIso X U').app ((derivedPullback s).obj M)) from by
      apply Iso.ext
      simpa only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
        Iso.app_hom] using
        singleComplexOpenPullbackSquareIso_hom_app_eq_compositionTo s U U' j hj M)
  simpa only [Iso.app_inv, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, Iso.app_hom, Category.assoc] using h

end AlgebraicGeometry
