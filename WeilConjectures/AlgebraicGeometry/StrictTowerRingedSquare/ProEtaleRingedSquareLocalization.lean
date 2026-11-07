/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerOperationsSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalDerivedPullbackNormalization

set_option linter.privateModule false

/-! The canonical ringed inverse-image square is exact localization of its ordinary square.
Source: Stacks Project, Tag 0D6D.
(blueprint: lem-weil-pbc-ringed-square-localization) -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
universe t
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  proEtaleRingModulePullback proEtaleRingModuleAdjunction proEtaleRingCompositeCoefficients
  proEtaleCanonicalDerivedPullbackComparison

private theorem localization_transport
    {U V : Scheme.{t}} (R : Sheaf (ProEt.topology V) CommRingCat.{t + 1})
    (S : Sheaf (ProEt.topology U) CommRingCat.{t + 1})
    {a b : Σ q : U ⟶ V,
      (proEtaleSheafInverseImage q CommRingCat.{t + 1}).obj R ≅ S} (h : a = b) :
    Functor.mapDerivedCategoryNatIso (eqToIso (congrArg
        (fun z ↦ proEtaleRingModulePullback z.1 R S z.2) h)) =
      eqToIso (congrArg (fun z ↦ proEtaleRingDerivedPullback z.1 R S z.2) h) := by
  cases h
  apply Iso.ext
  exact Functor.mapDerivedCategoryNatIso_refl

end AlgebraicGeometry.Scheme
