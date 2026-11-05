/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomDataSupplement
public import WeilConjectures.CategoryTheory.ClosedScalarHom.ClosedScalarHomComparison
public import WeilConjectures.CategoryTheory.Scalar.ScalarHomCanonicalIso
import WeilConjectures.CategoryTheory.ClosedScalarHom.ClosedScalarHomComposition
import WeilConjectures.CategoryTheory.ClosedScalarHom.ClosedScalarHomTransport
import WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence

/-! # Canonical scalar tensor comparisons and coefficient towers

Source: Stacks 07A4, 07A6 and 0D6D. The internal-Hom map occurring in the
coherence equations is the explicitly constructed map of the five Hom bijections.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open WeilConjectures SheafOfModules
namespace CategoryTheory
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ R : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J R)]
  (M : ScalarHomModels.{c, v, r, w} J) {R S : Sheaf J CommRingCat.{max c v r}}

end CategoryTheory
