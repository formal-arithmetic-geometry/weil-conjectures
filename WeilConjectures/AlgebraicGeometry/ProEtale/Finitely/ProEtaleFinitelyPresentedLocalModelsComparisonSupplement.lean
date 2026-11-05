/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finitely.ProEtaleFinitelyPresentedLocalModels
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleEncoding
public import WeilConjectures.CategoryTheory.ConstantRingModuleSheaves
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantModuleSheaf
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageSupplement
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleFinitelyPresentedLocalModelsComparison

/-! # Finitely presented local constant models on the pro-etale site

Source: Stacks Project, Tags 09AJ and 093U.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

namespace ProFiniteModels

attribute [local instance] asSmallDownEquivalence asSmallUpEquivalence

attribute [local instance] asSmallDense

attribute [local instance] asSmallDownEquivalence asSmallUpEquivalence
  asSmallDense asSmallUpDense

end ProFiniteModels

attribute [local instance] ProFiniteModels.asSmallDownEquivalence
  ProFiniteModels.asSmallUpEquivalence ProFiniteModels.asSmallDense
  ProFiniteModels.asSmallUpDense

end AlgebraicGeometry.Scheme
