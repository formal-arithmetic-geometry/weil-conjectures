/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.CategoryTheory.DerivedLimitRoosAbelianGroups
public import Sheaf.CategoryTheory.Limits.TowerLimitAdditiveLeftExact
import Sheaf.Algebra.Category.ModuleCat.TowerLimitExactSurjectiveKernels
import Sheaf.CategoryTheory.Abelian.HorseshoeDeltaFunctor
import Sheaf.CategoryTheory.InjectiveSplitTower
import Sheaf.CategoryTheory.InjectiveTowerEmbedding

/-!
# Acyclicity of inverse limits for surjective towers

Source: Stacks Project, More on Algebra, Lemma 15.88.1 (3), Tag 07KW
(blueprint: lem-pc-tower-surjective-lim-acyclic).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

attribute [local instance] roosTowerEnoughInjectives

/-- Additivity of inverse limit, supplied by `lem-pc-tower-limit-left-exact`.
Source: Stacks Project, Tag 07KW, Lemma 15.88.1 setup
(blueprint: lem-pc-tower-surjective-lim-acyclic). -/
noncomputable local instance towerLimitAdditiveInstance :
    (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).Additive :=
  towerLimitAdditiveLeftExact.1

/-- Towers of abelian groups with surjective transitions are right acyclic for inverse limits.

Source: Stacks Project, Tag 07KW, Lemma 15.88.1 (3).
(blueprint: lem-pc-tower-surjective-lim-acyclic).

Proof, following the node:
1. By `lem-pc-tower-injective-embedding`, embed `B` into a tower `I` whose groups
are injective and whose transitions are split surjections. Its quotient `Q = I/B`
has surjective transitions: lift a representative along a transition of `I` and
pass to its class. This gives a short exact sequence of towers by
`lem-pc-tower-abelian`.
2. By `lem-pc-injective-split-tower-injective`, `I` is injective in the tower
category. Resolving it by the identity in degree zero gives vanishing higher
limits, using `def-sp-left-exact-additive`. Since `B` has surjective transitions,
`lem-weil-pbc-tower-limit-exact-surjective-kernels` (b), with ring the integers,
makes `lim I → lim Q` surjective. Apply the long exact sequence of
`lem-weil-pbc-horseshoe-delta-functor` (2); its hypotheses follow from
`lem-pc-tower-enough-injectives` and `lem-pc-tower-limit-left-exact`.
The segment `lim I → lim Q → R¹ lim B → R¹ lim I = 0` gives `R¹ lim B = 0`.
3. For `q ≥ 2`, the same sequence gives `R^q lim B ≅ R^(q-1) lim Q`, since
both adjacent higher limits of `I` vanish. The quotient `Q` is again surjective
by step 1. Induction on `q`, with step 2 as the base for every surjective tower,
therefore gives vanishing in every positive degree. -/
theorem surjectiveTowerLimitAcyclic (B : ℕᵒᵖ ⥤ AddCommGrpCat.{u})
    (hB : ∀ n : ℕ,
      Function.Surjective (B.map (homOfLE (Nat.le_add_right n 1)).op)) :
    ∀ q : ℕ, 1 ≤ q →
      IsZero (((lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).rightDerived q).obj B) := by
  sorry

end CategoryTheory
