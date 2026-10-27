/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Paper.ReconstructedPairRefinementData

/-! # Reconstructed RefinementSingleDegree

Source: blueprint sk-prop-sp-unique-adjoint, categorical proof, and
sk-thm-purity-transport Steps 2--4
(blueprint: lem-pur-reconstructed-refinement-single-degree).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
attribute [-instance] WeilConjectures.integralExceptionalSystemDerived
attribute [-instance] WeilConjectures.integralExceptionalLevelDerived
attribute [local instance 5000] AlgebraicGeometry.strictEtaleLevelDerived
  AlgebraicGeometry.strictEtaleSystemDerived
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
open WeilConjectures CompactSupportCondensedRealization PurIntegralSupportComparison
namespace WeilConjectures.ReconstructedPairRefinement
variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  (C : ComparisonFamily l k)
  (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
  [f.IsOver (Spec (.of k))]

/-- Detection of the supplied Brown square in one common cohomological degree.
Source: Stacks Tags 06XS and 08J5; parent proof Step 4.
Proof: exact conservative evaluations detect that both supplied systems are
concentrated in degree r. Their good-truncation maps identify them with the shifted
heart. The target is isomorphic to the first supplied system via theta, so it is
concentrated in that same degree. On the shifted heart the degree-r cohomology
functor is fully faithful. The exact evaluation comparisons carry its map to the
cohomology of each displayed evaluated map. Joint faithfulness of evaluation on
ordinary strict coefficient systems identifies these heart maps. Full faithfulness
of the shifted heart then gives the asserted equality in the derived category.
No faithfulness of evaluations on arbitrary derived morphisms is asserted.
(blueprint: lem-pur-reconstructed-refinement-single-degree). -/
theorem reconstructedRefinementSingleDegree :
    (∀ (c d : Compactification f)
    (D₁ : At l E k C X Y f c) (D₂ : At l E k C X Y f d) (w : c.Refinement d)
    (L : CondensedERealization.Integral l E Y.scheme)
    (A₁ : D₁.Supplied L) (A₂ : D₂.Supplied L) (r : ℤ)
    (s : A₂.system ≅ A₁.system),
    (∀ n : ℕ, ((D₁.transport.siteX.proEvaluation.evaluation n).obj A₁.system).IsGE r ∧
      ((D₁.transport.siteX.proEvaluation.evaluation n).obj A₁.system).IsLE r) →
    (∀ n : ℕ, ((D₁.transport.siteX.proEvaluation.evaluation n).obj A₂.system).IsGE r ∧
      ((D₁.transport.siteX.proEvaluation.evaluation n).obj A₂.system).IsLE r) →
    (∀ n : ℕ, (D₁.transport.siteX.proEvaluation.evaluation n).map
        (s.hom ≫ (D₁.pair L A₁).theta.hom) =
      (D₁.transport.siteX.proEvaluation.evaluation n).map
        ((D₂.pair L A₂).theta.hom ≫ mate D₁ D₂ w L A₁ A₂)) →
    s.hom ≫ (D₁.pair L A₁).theta.hom =
      (D₂.pair L A₂).theta.hom ≫ mate D₁ D₂ w L A₁ A₂) := by sorry

end WeilConjectures.ReconstructedPairRefinement
