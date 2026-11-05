/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityDerivedPullSingle
public import WeilConjectures.WeilSheaf.SmoothPuritySingleDatumSquare

/-! # Deriving a compatible geometric and coefficient datum on flat objects -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The nonflat derived coefficient comparison carries an ordinary datum square
to degree zero. The coefficient comparisons are computed on flat objects, and
the geometric pullbacks use their exact-functor identifications. -/
lemma purity_derived_flat_datum_square
    {M : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
    {M' : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    {N : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ' Y)}
    {N' : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X)}
    (hM : ObjectProperty.flat M) (hM' : ObjectProperty.flat M')
    (u : (g)^*⟦Λ⟧.obj M ⟶ M') (v : (g)^*⟦Λ'⟧.obj N ⟶ N')
    (r : (Mod.extendScalars (coefficientMap a Y)).obj M ⟶ N)
    (s : (Mod.extendScalars (coefficientMap a X)).obj M' ⟶ N')
    (h : (pullIso a g).inv.app M ≫
        (Mod.extendScalars (coefficientMap a X)).map u ≫ s = (g)^*⟦Λ'⟧.map r ≫ v) :
    (derivedUpperStarExtendScalarsIso a g).inv.app ((DerivedCategory.singleFunctor _ 0).obj M) ≫
        L(Mod.extendScalars (coefficientMap a X)).map
          ((leftDerivedUpperStarIsoMapDerivedCategory Λ g).hom.app
              ((DerivedCategory.singleFunctor _ 0).obj M) ≫
            (((g)^*⟦Λ⟧).mapDerivedCategorySingleFunctor 0).hom.app M ≫
            (DerivedCategory.singleFunctor _ 0).map u) ≫
        ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctorSingleFunctorIsoOfFlat
          hM').hom ≫ (DerivedCategory.singleFunctor _ 0).map s =
      L((g)^*⟦Λ'⟧).map
          (((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctorSingleFunctorIsoOfFlat
            hM).hom ≫ (DerivedCategory.singleFunctor _ 0).map r) ≫
        (leftDerivedUpperStarIsoMapDerivedCategory Λ' g).hom.app
          ((DerivedCategory.singleFunctor _ 0).obj N) ≫
        (((g)^*⟦Λ'⟧).mapDerivedCategorySingleFunctor 0).hom.app N ≫
        (DerivedCategory.singleFunctor _ 0).map v := by
  have hs := purity_single_datum_square
    (Mod.extendScalars (coefficientMap a Y)) (g)^*⟦Λ'⟧ (g)^*⟦Λ⟧
    (Mod.extendScalars (coefficientMap a X))
    L(Mod.extendScalars (coefficientMap a Y)) L((g)^*⟦Λ'⟧) L((g)^*⟦Λ⟧)
    L(Mod.extendScalars (coefficientMap a X))
    (purityExtendScalarsSingleComparison a Y)
    (purityPullbackSingleComparison Λ' g) (purityPullbackSingleComparison Λ g)
    (purityExtendScalarsSingleComparison a X)
    (derivedUpperStarExtendScalarsIso a g).inv (pullIso a g).inv u v r s
    (derivedUpperStarExtendScalarsIso_inv_app_single_comp_comparison a g M) h
  simpa only [purityPullbackSingleComparison_app_eq_exact,
    purityExtendScalarsSingleComparison_app_eq_of_flat _ _ hM,
    purityExtendScalarsSingleComparison_app_eq_of_flat _ _ hM',
    leftDerivedUpperStarIsoMapDerivedCategory, Category.assoc] using hs

end AlgebraicGeometry.ProEtale.CondensedRing
