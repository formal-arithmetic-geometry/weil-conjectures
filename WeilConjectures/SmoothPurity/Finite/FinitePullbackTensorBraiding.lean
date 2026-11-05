/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
import WeilConjectures.Algebra.Homology.Ringed.RingedTensorComplexConstraintsSupplement
import WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits

/-! # Signed total and derived braiding

Source: Stacks 06YS (K-flat resolutions), the symmetry paragraph after
06YU (definition-derived-tor), and More on Algebra 0FNG, item-flip-tensor-product.
(blueprint: def-pur-finite-pullback-tensor-braiding).
The constructions and their existing uniqueness proofs are extracted unchanged.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v
open CategoryTheory
open scoped MonoidalCategory
namespace WeilConjectures

section SignedBraiding
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local implicit_reducible] Functor.map₂HomologicalComplex
attribute [local instance 4000] HomologicalComplex.monoidalCategoryStruct
  HomologicalComplex.monoidalCategory
attribute [local irreducible] CochainComplex.Monoidal.braiding
  SheafOfModules.monoidalCategory PresheafOfModules.sheafificationAdjunction
  SheafOfModules.tensorObjIsoSheafification
universe a b

variable {C : Type (u + 1)} [Category.{u} C]
  (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  (A : Sheaf J CommRingCat.{u + 1})

attribute [local irreducible] pullbackTensorNative pullbackTensorNativeIso

attribute [local irreducible] pullbackTensorSignedTotal coefficientTotalTensor

variable [EssentiallySmall.{u + 1} C]
  [HasDerivedCategory.{u + 2} (SheafOfModules.{u + 1}
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A))]
  (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{u + 1, u, u, u + 2} J A))
  (T : CoefficientTensorModels.{u, u + 1, u, u + 2} J A S)

end SignedBraiding

attribute [local irreducible] pullbackTensorBraiding pullbackTensorSignedTotal
  coefficientTotalTensor

end WeilConjectures
