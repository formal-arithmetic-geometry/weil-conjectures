/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IsomorphismScalarCompletedModelBase
public import Sheaf.Paper.ScalarPullbackStrictConeData
import Sheaf.Paper.ScalarPullbackStrictConeNaturality

/-! # Chain-level data for the completed scalar formula

Source: Stacks Project, sites-modules.tex, Tag 03EL; the strict scalar
pullback cone construction (blueprint: lem-weil-isomorphism-scalar-completed-formula-chain-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme WeilConjectures
open scoped ChangeOfRings
namespace AlgebraicGeometry.ProEtale.IsomorphismScalarTensor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]

/-- The strict cone construction supplies an invertible chain map on the good
sub-category, before its completed section formula is transported.  The
statement records only this chain-level existence and its normalization by the
specified cone map.

Source: Stacks Project, sites-modules.tex, Tag 03EL; strict scalar pullback
cone construction.
(blueprint: lem-weil-isomorphism-scalar-completed-formula-chain-data).
-/
theorem completed_formula_chain_data
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    ∃ D : ScalarPullbackStrictConeData l E L ι g,
      ∃ b : (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ≅
        (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g,
        (∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
          HEq (b.hom.app P)
            ((scalarPullbackConeMap l E L ι g D.level D.cone).app P.obj)) := by
  sorry

end AlgebraicGeometry.ProEtale.IsomorphismScalarTensor
