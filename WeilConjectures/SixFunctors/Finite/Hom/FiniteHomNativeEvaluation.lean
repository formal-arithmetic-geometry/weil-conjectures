/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomNativeClosed
public import WeilConjectures.AlgebraicGeometry.CoefficientPairingChange.InternalAdjunctionPairingChange
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomEtaleBraidedEvaluation
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomScalarTensorBraid

/-! # Native evaluation equation for scalar extension
Source: blueprint thm-coef-finite-hom, evaluation paragraph
(blueprint: lem-coef-finite-hom-native-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u a b c d w z
open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard

-- Retain named tensor fields instead of expanding the derived bifunctor.
set_option allowUnsafeReducibility true in
attribute [local irreducible] DerivedMonoidal.tensorObjAux
  DerivedMonoidal.whiskerLeftAux DerivedMonoidal.whiskerRightAux

-- Use the coefficient and sheaf braidings fixed in the ordinary derived tensor.
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000]
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall

attribute [local implicit_reducible] CategoryTheory.uniformProd
  Etale.sheafMonoidalCategory Etale.sheafBraidedCategory Etale.sheafMonoidalClosed
  ModuleCat.MonoidalCategory.symmetricCategory SymmetricCategory.ofFaithful

attribute [local implicit_reducible]
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

attribute [local implicit_reducible]
  DerivedCategory.monoidalClosed_of_hasFunctorialFlatResolution

-- Keep the faithful-transfer construction atomic after exposing the symmetric parent.
attribute [local irreducible] ModuleCat.MonoidalCategory.instBraidedCategory

attribute [local irreducible] DerivedCategory.monoidalClosed

end WeilConjectures
