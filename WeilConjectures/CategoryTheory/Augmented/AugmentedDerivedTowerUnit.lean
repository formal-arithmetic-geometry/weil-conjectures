/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.HasLimits

/-! # The augmented derived tower unit

Source: Stacks Project, Tag 099M (`proetale.tex`, lemma-naive-completion),
agent-written categorical refinement of the canonical completion-map construction
(blueprint: lem-weil-pbc-augmented-derived-tower-unit).

## Main statements

- `CategoryTheory.exists_augmentedDerivedTowerUnit`: the two unique natural lifts and
  their ordinary-unit normalization at every object.
- `CategoryTheory.towerAugmentation_ordinaryUnit`: for strict towers, the ordinary
  unit followed by the limit of the augmentation is the map of its augmentation cone.

The functor `RF` and comparison `γ` are supplied data. The property
`CategoryTheory.IsDerivedLimit` alone does not choose either of them.
-/

@[expose] public section

universe u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃

namespace CategoryTheory

end CategoryTheory
