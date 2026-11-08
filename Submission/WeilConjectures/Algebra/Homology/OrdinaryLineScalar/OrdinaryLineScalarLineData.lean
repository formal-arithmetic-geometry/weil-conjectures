/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.Algebra.Homology.OrdinaryLineScalar.OrdinaryLineScalarData
import all Submission.WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import all Submission.WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
import all Submission.WeilConjectures.Algebra.Homology.LineUnbounded.LineUnboundedDerivedTensor

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Ordinary signed-line tensor and derived scalar extension

Source: Stacks Project, Tags 07A4, 0G7E and 0D6D; blueprint main-20261015,
Tate-twist local freeness, proof (3).
(blueprint: lem-pur-ordinary-line-scalar-line-data)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe t a w u v b r ua va
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
-- Prefer the native additive structures over routes through abelian instances.
attribute [local instance 30000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive CategoryTheory.functorCategoryPreadditive
  CategoryTheory.Preadditive.preadditiveHasZeroMorphisms
  CategoryTheory.Functor.preservesZeroMorphisms_of_additive
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
namespace SheafOfModules.OrdinaryLineScalar

variable (X : Scheme.{t}) [EssentiallySmall.{max a (t + 1)} X.ProEt]

variable {X}
  [∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)},
    HasDerivedCategory.{w} (Modules.{t, a} X R)]
local notation "𝒬[" R "]" => (DerivedCategory.Q (C := Modules X R))
attribute [local instance] modulesCategory modulesAbelian monoidalCategory
attribute [local implicit_reducible] monoidalCategory
attribute [local irreducible] LineUnbounded.derived LineUnbounded.normalization
  KFlatFixedTensor.representativeIso compute signedLinePower scalarTensorPower
  LineUnbounded.localizedCancellation LineUnbounded.cancellation
  LineUnbounded.pureTensor ScalarHomOrdinary.pure

set_option backward.isDefEq.respectTransparency.types false

section LineConstruction

set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] monoidalCategory
  tensorObjIsoSheafification PresheafOfModules.sheafificationAdjunction

section PureTensorFormula

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]

end PureTensorFormula

private def tensor_site
    {R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}
    (M N : Modules.{t, a} X R) :=
  ScalarHomOrdinary.tensorIsoSite.{t + 1, t, max a (t + 1)} R M N

attribute [local irreducible] tensor_site

section
attribute [local semireducible] monoidalCategory signedLinePower scalarTensorPower
end

attribute [local semireducible] monoidalCategory

end LineConstruction

end SheafOfModules.OrdinaryLineScalar
