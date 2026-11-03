/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrderedAffineTranspose.OrderedAffineTransposeData
import WeilConjectures.AlgebraicGeometry.AffineLineEvaluation.AffineLineCompositeTranspose
import all WeilConjectures.SixFunctors.Exceptional.ExceptionalFiniteRestrictionAdjunction

/-! # Naturality of the ordered affine comparison

Source: the ordered affine transpose proof, Step 2.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v₁ v₂ w₁ w₂
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.OrderedAffineTranspose
open AffineLinePurity AffineSpacePurity VectorIntegrationSite

attribute [local semireducible] orderedSource exceptional lineSource twistAction
  projectionSourceObject projectionTargetObject
attribute [local implicit_reducible] orderedSource exceptional twistAction
  iteratedAffineLine iteratedAffineLineProj
set_option allowUnsafeReducibility true in
attribute [local reducible] lineSource projectionSourceObject projectionTargetObject
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  Scheme.finiteEtaleTateLine DerivedCategory.TStructure.t
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  DerivedCategory.singleFunctors

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2 AffineSpacePurity.C._proof_1 AffineSpacePurity.C._proof_2

set_option maxHeartbeats 1600000 in
-- Identifying the chosen reassociation with its explicit tensor formula is expensive.
set_option maxHeartbeats 400000 in
-- Specializing the three bounded-below Hom equivalences fixes their derived categories.
set_option maxHeartbeats 1600000 in
-- The chosen inverse compositor is compared with its explicit value along the tower.
attribute [local irreducible] Adjunction.ofIsLeftAdjoint Adjunction.homEquiv
  CategoryTheory.Functor.rightAdjoint fixedCompactSupportComparisonIso specifiedExceptionalHomEquiv
  derivedComparisonAdjunction

private theorem paste_two {Cat : Type*} [Category* Cat]
    {A B C A' B' C' : Cat} {s : A ⟶ A'} {t : B ⟶ B'} {v : C ⟶ C'}
    {a : A ⟶ B} {a' : A' ⟶ B'} {b : B ⟶ C} {b' : B' ⟶ C'}
    (ha : s ≫ a' = a ≫ t) (hb : t ≫ b' = b ≫ v) :
    s ≫ (a' ≫ b') = (a ≫ b) ≫ v := by
  rw [← Category.assoc, ha, Category.assoc, hb, ← Category.assoc]

end AlgebraicGeometry.ProEtale.OrderedAffineTranspose
