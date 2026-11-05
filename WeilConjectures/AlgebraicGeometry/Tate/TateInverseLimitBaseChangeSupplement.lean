/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageTensorHom
public import Mathlib.NumberTheory.Padics.RingHoms
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingPullbackComparison
public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerOperationsSupplement

/-!
# Base change of an inverse-limit tower and its finite tensor reduction

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-def-purity-conv/lem-pur-finite-kummer-level.proof.md, final sentence;
Stacks Project, Tags 03DB, 03CO and 03EL
(blueprint: lem-pur-tate-inverse-limit-base-change).

The index `op r` denotes the positive level `r + 1`. Scalar extension is the
recorded sheaf tensor construction, with its pure tensors written in the order `a ⊗ x`.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] proEtaleRingModulePullback proEtaleModuleInverseImage
  proEtaleRingModuleAdjunction

-- Keep the tensor universal-property inverse folded after establishing its API.
-- Otherwise later equivalence comparisons unfold its sectionwise tensor construction.
attribute [local irreducible] restrictionToTensor

attribute [local irreducible] tensorUnit

attribute [local irreducible] tensorHomEquiv tensorPresheafHomEquiv tensorToRestriction

attribute [local irreducible] reductionUnit

end AlgebraicGeometry.Scheme
