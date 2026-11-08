/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison
public import Submission.WeilConjectures.Algebra.Homology.HomTensorDegreewise
public import Submission.WeilConjectures.Algebra.Homology.NormalizedHomComplexGlobalCochains
import Submission.WeilConjectures.Algebra.Homology.HomTensorDifferential
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Submission.WeilConjectures.Algebra.Homology.HomTensorDegreewise
import Submission.WeilConjectures.Algebra.Homology.NormalizedHomComplexGlobalCochains

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # The pure-tensor component calculation for ordinary cochains

Source: Stacks Project, sites-cohomology.tex, Tag 0A90 (lemma-compose).
(blueprint: lem-pc-normalized-tensor-hom-cochain-components).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open CochainComplex.HomComplex
namespace AlgebraicGeometry

attribute [local irreducible] SheafOfModules.tensorHomEquiv homTensorCurrySectionMap
  SheafOfModules.tensorObjIsoSheafification
  PresheafOfModules.sheafificationAdjunction
  SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
  homComplex homTensorDegreewiseMap normalizedHomGlobalCochains
  normalizedHomFactorEquiv normalizedHomProjection homTensorCurryProjection

section TensorHelpers

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  (R : Sheaf J CommRingCat.{u})

set_option hygiene false in
local notation "𝓡" => (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
set_option hygiene false in
local notation "Mod" => SheafOfModules.{u} 𝓡

-- Identify the two APIs before specializing the complex arguments.
-- Expose section evaluation with abstract module arguments, without reducing complexes.
end TensorHelpers

end AlgebraicGeometry
