/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleObjectInverseImageRestrictionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
public import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomDataSupplement
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtale.Scalar.ProEtaleScalarExtensionSliceComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientSliceComparisonData

/-! # Closed slice comparison with transported pro-etale coefficients

Comparison data and their defining section and representative equations
(blueprint: def-zl-proetale-slice-comparison-data).

Source: Hemo--Richarz--Scholbach, Lemma 4.5, and Stacks Project, Tags 03CE,
03EL, 07A4, 08J7, 08J9, 08JB and 0FPT
(blueprint: lem-zl-proetale-coefficient-slice-closed-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u u₁ v₁ u₂ v₂
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] CoefficientTensorModels.iso

namespace ProEtaleCoefficientSliceComparison

variable {X : Scheme.{u}} (U : X.ProEt)
  (O : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (B : Sheaf (ProEt.topology U.left) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage U.hom CommRingCat.{u + 1}).obj O ≅ B)
  (delta : ProEtaleObjectRestrictionComparison U CommRingCat.{u + 1})

variable (S : CoefficientClosedStructure (proEtaleCoefficientHom X O))
  (SR : CoefficientClosedStructure (proEtaleCoefficientHom U.left (proEtaleSliceRing U O)))
  (SB : CoefficientClosedStructure (proEtaleCoefficientHom U.left B))
  (T : CoefficientTensorModels.{u + 1, u + 1, u} (ProEt.topology X) O S)
  (TR : CoefficientTensorModels.{u + 1, u + 1, u} (ProEt.topology U.left)
    (proEtaleSliceRing U O) SR)
  (TB : CoefficientTensorModels.{u + 1, u + 1, u} (ProEt.topology U.left) B SB)

end ProEtaleCoefficientSliceComparison

end AlgebraicGeometry.Scheme
