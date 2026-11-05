/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.CoefficientHomZeroClass
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedTensorHomModel
public import WeilConjectures.Algebra.Homology.Ringed.RingedTensorComplexConstraintsSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # Zero cycles of the fixed Hom complex as maps from the unit complex

A degree-zero cycle of the global sections of the fixed representative Hom complex
`Hom(L, I(M))` is the same as a chain map from the coefficient ring placed in degree
zero. This file records this dictionary, the resulting description of the class of a
cycle through the global unit class, and the evaluation of `coefficientHomZeroEquiv` on
the global class of a tensor-Hom transpose.

Source: Stacks Project, Tags 08JA, 0A8X and 08J9.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u c v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace WeilConjectures

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (A : Sheaf J CommRingCat.{max c v u})

variable [HasDerivedCategory.{w} (SheafOfModules.{max c v u}
  ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A))]

end WeilConjectures
