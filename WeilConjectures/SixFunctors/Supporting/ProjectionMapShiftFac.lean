/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapShift
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ShiftComparison
public import WeilConjectures.CategoryTheory.Monoidal.KFlatEquivalence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import WeilConjectures.SixFunctors.Monoidal.MonoidalComplex
public import WeilConjectures.SixFunctors.Monoidal.MonoidalRightCounit
public import WeilConjectures.SixFunctors.Monoidal.MonoidalIso
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-!
# The tensor comparison of `Lp^*` on K-flat complexes

Auxiliary part of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapShift`.
The results it used to hold are now provided by upstream's monoidal structure of `Lf^*`, with the
same statements, and this module only imports them:

- `AlgebraicGeometry.ProEtale.CondensedRing.isEquivalence_extendScalars_condensedPullbackHom`,
  `AlgebraicGeometry.ProEtale.CondensedRing.kFlat_upperStar_mapHomologicalComplex_obj`,
  `AlgebraicGeometry.ProEtale.CondensedRing.kFlat_upperStar_mapHomotopyCategory_obj`
  (`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalComplex`);
- `AlgebraicGeometry.ProEtale.CondensedRing.upperStarTensorComplexHom_δ`,
  `AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarTensorRightCounit_app_app`
  (`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalRightCounit`);
- `AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarTensor_app_app_fac`
  (`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalIso`).
-/
