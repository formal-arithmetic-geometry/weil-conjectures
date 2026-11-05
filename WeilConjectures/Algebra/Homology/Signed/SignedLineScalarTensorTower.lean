/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionDualTowerCore
import WeilConjectures.Algebra.Homology.SixFunctors.LocalizedSiteTensorRestrictionSupplement
import all WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionDualLocalIso
import WeilConjectures.Mathlib.CategoryTheory.Sites.LocallySurjective

/-! # Signed powers of lines: scalar, tensor and tower comparisons

Source: blueprint main-20261015, prop-weil-twist-preserves.proof.md, tensor-power/internal-Hom
and common-finite-stage sentences; Stacks Project, Tags 03EK, 04TT and 0GMX.
(blueprint: lem-pur-signed-line-scalar-tensor-tower)

The coefficient and module universe is `max uC vC u`, so slice internal Homs stay in that
universe without equating the site's object and morphism universes. The scalar-extension
API puts the scalar first: `scalarExtensionSection α M U s x` denotes `x tensor s` in the
right-scalar convention of the node. Normalizations below refer to actual sheafified tensors.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.all false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe uC vC u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace SheafOfModules

set_option linter.unusedSectionVars false
section CoefficientUniverses

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [UnivLE.{max uC vC, u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [hSliceSheafify : ∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

set_option allowUnsafeReducibility true in
attribute [local reducible] sheafCompose ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj' SheafOfModules.unit PresheafOfModules.unit
  scalarTensorPower PresheafOfModules.restrictOver
  Functor.sheafPushforwardContinuous SheafOfModules.overFunctor
  SheafOfModules.pushforward PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀ PresheafOfModules.pushforward₀Obj
  PresheafOfModules.restrictScalars PresheafOfModules.restrictScalarsObj Over.forget

attribute [local irreducible] siteSheafTensorRight siteSheafTensorTmul
  siteSheafTensorSecondMap scalarExtensionDualMap changeOfRingsOfUniverses
  changeOfRingsHomOfUniverses scalarExtensionLift scalarExtensionSection

attribute [local irreducible] scalarTensorBinaryIso scalarTensorBinaryForward
  scalarTensorBinaryInverse scalarTensorLeftUnitor scalarExtensionUnitIso
  scalarExtensionTowerForward scalarExtensionTowerReverse

attribute [local irreducible] tensorSecondIso

attribute [local irreducible] basisChart

attribute [local irreducible] tensorUnitChart

attribute [local irreducible] dualBasis

end CoefficientUniverses

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max uC vC u} RingCat.{max uC vC u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
  [HasWeakSheafify J AddCommGrpCat.{max uC vC u}]

variable [∀ X : C,
  (J.over X).WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] sheafCompose ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj' SheafOfModules.unit PresheafOfModules.unit
  scalarTensorPower signedLinePower PresheafOfModules.restrictOver
  Functor.sheafPushforwardContinuous SheafOfModules.overFunctor
  SheafOfModules.pushforward PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀ PresheafOfModules.pushforward₀Obj
  PresheafOfModules.restrictScalars PresheafOfModules.restrictScalarsObj Over.forget

attribute [local irreducible] siteSheafTensorRight siteSheafTensorTmul
  siteSheafTensorSecondMap scalarExtensionDualMap changeOfRingsOfUniverses
  changeOfRingsHomOfUniverses scalarExtensionLift scalarExtensionSection

attribute [local irreducible] tensorSecondIso basisChart
  scalarTensorBinaryIso scalarTensorBinaryForward scalarTensorBinaryInverse
  scalarTensorLeftUnitor scalarExtensionUnitIso
  scalarExtensionTowerForward scalarExtensionTowerReverse

attribute [local irreducible] positiveComparison

attribute [local irreducible] signedComparison

set_option allowUnsafeReducibility true in
attribute [local semireducible] scalarTensorPower signedLinePower

set_option allowUnsafeReducibility true in
attribute [local irreducible] scalarTensorPower signedLinePower

set_option allowUnsafeReducibility true in
attribute [local semireducible] scalarTensorPower signedLinePower

set_option allowUnsafeReducibility true in
attribute [local irreducible] scalarTensorPower signedLinePower

attribute [local irreducible] signedProductChart

set_option allowUnsafeReducibility true in
attribute [local semireducible] scalarTensorPower signedLinePower

end SheafOfModules
