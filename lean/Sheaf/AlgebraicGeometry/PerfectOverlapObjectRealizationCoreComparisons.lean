/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreComparisons

/-! # Component API for the canonical overlap comparisons

The adopted source library supplies the comparison constructions. This adapter
retains the four component equations needed by the overlap cube without
redeclaring the source constructions.
Source: Stacks Project, Tags 08DW and 0D5S.
(blueprint: def-pc-perfect-overlap-core-comparisons-api).
-/

@[expose] public section

set_option autoImplicit false

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

section

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
  exact (Iso.hom_eq_inv ((openPullbackRestrictionIso g P U h).app M)
    ((singleComplexOpenPullbackSquareIso g U P (g.resLE U P h)
      (Scheme.Hom.resLE_comp_ι g h)).app M)).2
    (openPullbackRestrictionIso_inv_app_eq_square g P U h M).symm

section

variable [∀ (Z : Scheme.{u}) (U : Z.Opens),
  HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]

attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian

/-- The canonical restriction/pullback component is the inverse pinned open
square, transported into the localized site and preceded by its return unit. -/
theorem perfectOverlapRestrictionBeta_hom_app_square
    {X Y : Scheme.{u}} (g : X ⟶ Y) (P : X.Opens) (U : Y.Opens)
    (h : P ≤ g ⁻¹ᵁ U) (M : schemeDerivedCategory Y) :
    (perfectOverlapRestrictionBeta g U P h).hom.app M =
      (openSiteReturnIso X P).inv.app ((derivedPullback g).obj M) ≫
        (overlapSiteInverse P).mapDerivedCategory.map
          ((singleComplexOpenPullbackSquareIso g U P (g.resLE U P h)
            (Scheme.Hom.resLE_comp_ι g h)).inv.app M) := by
  rw [perfectOverlapRestrictionBeta_hom_app,
    openPullbackRestrictionIso_hom_app_eq_square_inv]

/-- The inverse canonical restriction/pullback component is the forward
pinned open square, followed by the site return map. -/
theorem perfectOverlapRestrictionBeta_inv_app_square
    {X Y : Scheme.{u}} (g : X ⟶ Y) (P : X.Opens) (U : Y.Opens)
    (h : P ≤ g ⁻¹ᵁ U) (M : schemeDerivedCategory Y) :
    (perfectOverlapRestrictionBeta g U P h).inv.app M =
      (overlapSiteInverse P).mapDerivedCategory.map
        ((singleComplexOpenPullbackSquareIso g U P (g.resLE U P h)
          (Scheme.Hom.resLE_comp_ι g h)).hom.app M) ≫
        (openSiteReturnIso X P).hom.app ((derivedPullback g).obj M) := by
  rw [perfectOverlapRestrictionBeta_inv_app,
    openPullbackRestrictionIso_inv_app_eq_square]

end

end

end AlgebraicGeometry

