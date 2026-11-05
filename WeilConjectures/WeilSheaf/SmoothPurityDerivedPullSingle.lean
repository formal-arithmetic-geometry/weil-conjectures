/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPuritySingleCochainNormalization
public import WeilConjectures.WeilSheaf.SmoothPuritySingleModuleComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushResidueIsoComplex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.NonFlatPullMonoidal

/-! # The actual nonflat coefficient comparison on an object in degree zero -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- On an object in degree zero, the nonflat derived pullback comparison is the
ordinary coefficient/pullback comparison through the canonical single maps. -/
lemma derivedUpperStarExtendScalarsIso_inv_app_single_comp_comparison
    (M : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (derivedUpperStarExtendScalarsIso a g).inv.app ((DerivedCategory.singleFunctor _ 0).obj M) ≫
        L(Mod.extendScalars (coefficientMap a X)).map ((purityPullbackSingleComparison Λ g).app M) ≫
        (purityExtendScalarsSingleComparison a X).app ((g)^*⟦Λ⟧.obj M) =
      L((g)^*⟦Λ'⟧).map
          ((purityExtendScalarsSingleComparison a Y).app M) ≫
        (purityPullbackSingleComparison Λ' g).app
          ((Mod.extendScalars (coefficientMap a Y)).obj M) ≫
        (DerivedCategory.singleFunctor _ 0).map ((pullIso a g).inv.app M) := by
  have hfac (K) := derivedUpperStarExtendScalarsIso_inv_app_Qh_comp_counit a g K
  simp only [pullIsoInvHomotopy, Functor.mapHomotopyCategoryCommIsoHom_app] at hfac
  have hcochain := Functor.purityCochainComparisonOfHomotopy_square
    (Mod.extendScalars (coefficientMap a Y)) (g)^*⟦Λ'⟧ (g)^*⟦Λ⟧
    (Mod.extendScalars (coefficientMap a X))
    L(Mod.extendScalars (coefficientMap a Y)) L((g)^*⟦Λ'⟧) L((g)^*⟦Λ⟧)
    L(Mod.extendScalars (coefficientMap a X))
    (Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctorCounit
    ((g)^*⟦Λ'⟧).leftDerivedFunctorCounit ((g)^*⟦Λ⟧).leftDerivedFunctorCounit
    (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctorCounit
    (derivedUpperStarExtendScalarsIso a g).inv (pullIso a g).inv hfac
  have hsingle := Functor.puritySingleComparisonOfCochain_square
    (Mod.extendScalars (coefficientMap a Y)) (g)^*⟦Λ'⟧ (g)^*⟦Λ⟧
    (Mod.extendScalars (coefficientMap a X))
    L(Mod.extendScalars (coefficientMap a Y)) L((g)^*⟦Λ'⟧) L((g)^*⟦Λ⟧)
    L(Mod.extendScalars (coefficientMap a X))
    _ _ _ _ (derivedUpperStarExtendScalarsIso a g).inv (pullIso a g).inv hcochain M
  simpa only [Functor.puritySingleComparisonOfCochain_leftDerivedCounit,
    purityPullbackSingleComparison, purityExtendScalarsSingleComparison] using hsingle

end AlgebraicGeometry.ProEtale.CondensedRing
