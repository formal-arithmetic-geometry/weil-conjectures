/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpacePurity.AffineSpacePurityComparison
import WeilConjectures.AlgebraicGeometry.OrderedAffineTranspose.OrderedAffineComparisonNaturality

/-! # Naturality of the normalized affine-line comparison

Source: current blueprint, projection-purity agreement, final canonical reassociation;
expanded ordered-transpose proof Step 8.
(blueprint: lem-pur-affine-line-comparison-naturality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.AffineSpacePurity
open AffineLinePurity VectorIntegrationSite

attribute [local semireducible] orderedSource exceptional lineSource twistAction
attribute [local implicit_reducible] orderedSource exceptional lineSource twistAction
attribute [local implicit_reducible] iteratedAffineLine iteratedAffineLineProj
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  Scheme.finiteEtaleTateLine DerivedCategory.TStructure.t
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  DerivedCategory.singleFunctors

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2 AffineSpacePurity.C._proof_1 AffineSpacePurity.C._proof_2

section TensorNormalization
universe v w v' w'
variable {Cat : Type v} {Cat' : Type v'} [Category.{w} Cat] [Category.{w'} Cat']

end TensorNormalization

end AlgebraicGeometry.ProEtale.AffineSpacePurity
