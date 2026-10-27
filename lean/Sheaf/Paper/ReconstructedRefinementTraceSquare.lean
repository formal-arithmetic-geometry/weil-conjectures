/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Paper.ReconstructedPairRefinementData

/-! # Reconstructed RefinementTraceSquare

Source: blueprint sk-prop-sp-unique-adjoint, categorical proof, and
sk-thm-purity-transport Steps 2--4
(blueprint: lem-pur-reconstructed-refinement-trace-square).
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

/-- Reconstruction of the system counit square for supplied representing pairs.
Source: blueprint sk-prop-sp-unique-adjoint categorical proof, Transposes and
Uniqueness; parent proof Steps 4--5.
Proof: let e_i be the actual reduction/limit counit on the supplied systems.
Naturality gives R(sbar) followed by e_1 equal to e_2 followed by s.
The Brown Hom formula and the definition of mate give its counit equation.
Apply compact support to the supplied theta square, use that equation and
naturality of the constructed system comparison. Insert these identities in
PublishedFamily.trace_reduction for both traces, along with naturality of alpha
and its actual refinement square. The two reductions of the desired integral
maps now agree. Reduction on derived-complete objects is fully faithful by the
normalized reconstruction adjunction; hence the integral maps agree. Coordinate
equivalence preserves this calculation, including its counit factors.
(blueprint: lem-pur-reconstructed-refinement-trace-square). -/
theorem reconstructedRefinementTraceSquare :
    ∀ (c d : Compactification f)
    (D₁ : At l E k C X Y f c) (D₂ : At l E k C X Y f d) (w : c.Refinement d)
    (L : CondensedERealization.Integral l E Y.scheme)
    (A₁ : D₁.Supplied L) (A₂ : D₂.Supplied L) (s : A₂.system ≅ A₁.system),
    s.hom ≫ (D₁.pair L A₁).theta.hom =
      (D₂.pair L A₂).theta.hom ≫ mate D₁ D₂ w L A₁ A₂ →
    (support l E k C X Y f c).map (reconstructedMap D₁ D₂ L A₁ A₂ s.hom) ≫
      D₁.trace L A₁ =
        (comparison l E k C X Y f w).hom.app A₂.object ≫ D₂.trace L A₂ := by sorry

end WeilConjectures.ReconstructedPairRefinement
