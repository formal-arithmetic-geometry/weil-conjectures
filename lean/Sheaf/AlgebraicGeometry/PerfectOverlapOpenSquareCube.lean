/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreComparisons
public import Sheaf.AlgebraicGeometry.SingleComplexOpenPullbackCube

/-! # Pinned overlap and open-pullback squares -/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
/-- The inverse of the named open-pullback restriction comparison is the
componentwise pinned open square. Both use the same chosen pullback-composition
isomorphism; their open comparisons cancel in opposite order. -/
theorem openPullbackRestrictionIso_inv_app_eq_square
    {X Y : Scheme.{u}} (g : X ⟶ Y) (P : X.Opens) (U : Y.Opens)
    (h : P ≤ g ⁻¹ᵁ U) (M : schemeDerivedCategory Y) :
    (openPullbackRestrictionIso g P U h).inv.app M =
      (singleComplexOpenPullbackSquareIso g U P (g.resLE U P h)
        (Scheme.Hom.resLE_comp_ι g h)).hom.app M := by
  simp only [openPullbackRestrictionIso, singleComplexOpenPullbackSquareIso,
    NatIso.ofComponents_hom_app, Iso.trans_inv, NatTrans.comp_app,
    Iso.symm_inv, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.symm_hom, Iso.symm_inv, eqToIso.hom, eqToIso.inv, eqToHom_app]
  simp only [Category.assoc, perfectHomComposition,
    singleComplexOpenPinnedComposition]

/-- The forward named restriction comparison is the inverse pinned open
square component. This is the inverse of the preceding component equality. -/
theorem openPullbackRestrictionIso_hom_app_eq_square_inv
    {X Y : Scheme.{u}} (g : X ⟶ Y) (P : X.Opens) (U : Y.Opens)
    (h : P ≤ g ⁻¹ᵁ U) (M : schemeDerivedCategory Y) :
    (openPullbackRestrictionIso g P U h).hom.app M =
      (singleComplexOpenPullbackSquareIso g U P (g.resLE U P h)
        (Scheme.Hom.resLE_comp_ι g h)).inv.app M := by
  have he : (openPullbackRestrictionIso g P U h).symm.app M =
      (singleComplexOpenPullbackSquareIso g U P (g.resLE U P h)
        (Scheme.Hom.resLE_comp_ι g h)).app M := by
    apply Iso.ext
    exact openPullbackRestrictionIso_inv_app_eq_square g P U h M
  have := congrArg Iso.symm he
  exact congrArg Iso.hom this

end AlgebraicGeometry
