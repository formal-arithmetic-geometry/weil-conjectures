/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IsomorphismScalarCompletedModelBase
public import Sheaf.Paper.ScalarPullbackStrictConeData
import Sheaf.Paper.ScalarPullbackStrictConeNaturality

/-! # Transport of the chain normalization to completed sections

Source: Stacks Project, sites-modules.tex, Tag 03EL; normalized tensor
comparison after inverse-limit transport.
(blueprint: lem-weil-isomorphism-scalar-completed-formula-chain-normalization).
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

/-- The normalized strict cone map has the completed pure-tensor formula.
The cone data encode the finite projections and inverse-limit coordinates; this
step is the coordinate transport from those data to the displayed completed
section equation.

Source: Stacks Project, sites-modules.tex, Tag 03EL; inverse-limit scalar
transport and normalized pure tensors.
(blueprint: lem-weil-isomorphism-scalar-completed-formula-chain-normalization).
-/
theorem completed_formula_chain_normalization
    (D : ScalarPullbackStrictConeData l E L ι g)
    (b : (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ≅
      (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g)
    (hMap : ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
      HEq (b.hom.app P)
        ((scalarPullbackConeMap l E L ι g D.level D.cone).app P.obj)) :
    CompletedFormula l E L ι g b := by
  sorry

end AlgebraicGeometry.ProEtale.IsomorphismScalarTensor
