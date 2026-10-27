/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Paper.ReconstructedPairRefinementData

/-! # Reconstructed BrownMateLaws

Source: blueprint sk-prop-sp-unique-adjoint, categorical proof, and
sk-thm-purity-transport Steps 2--4
(blueprint: lem-pur-reconstructed-brown-mate-laws).
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

/-- Invertibility and composition of the actual transported Brown mates.
Source: blueprint sk-prop-sp-unique-adjoint categorical proof, Transposes and
Uniqueness; parent proof Steps 4 and 6.
Proof: the Brown Hom formula sends each defined mate to its prescribed system
comparison followed by the second counit. Define the reverse arrow by transposing
the inverse system comparison followed by the first counit under the second Hom
bijection. Both outputs lie in the common intrinsic origin domain. Naturality of
the system comparison and the two counit equations show that each composite has
the same transpose as the identity. Injectivity of the Brown Hom bijections proves
they are inverse. For three compactifications transpose the composite of mates;
use both counit equations, naturality, and composition of the intrinsic refinement
maps conjugated by beta. The resulting transpose is that of the direct mate, so
injectivity proves composition. These are equations of system maps.
(blueprint: lem-pur-reconstructed-brown-mate-laws). -/
theorem reconstructedBrownMateLaws :
    (∀ (c d : Compactification f)
    (D₁ : At l E k C X Y f c) (D₂ : At l E k C X Y f d) (w : c.Refinement d)
    (L : CondensedERealization.Integral l E Y.scheme)
    (A₁ : D₁.Supplied L) (A₂ : D₂.Supplied L), IsIso (mate D₁ D₂ w L A₁ A₂)) ∧
    (∀ (c d e : Compactification f)
    (D₁ : At l E k C X Y f c) (D₂ : At l E k C X Y f d) (D₃ : At l E k C X Y f e)
    (r : c.Refinement d) (s : d.Refinement e)
    (L : CondensedERealization.Integral l E Y.scheme)
    (A₁ : D₁.Supplied L) (A₂ : D₂.Supplied L) (A₃ : D₃.Supplied L),
    mate D₁ D₃ (r.comp s) L A₁ A₃ = mate D₂ D₃ s L A₂ A₃ ≫ mate D₁ D₂ r L A₁ A₂) := by sorry

end WeilConjectures.ReconstructedPairRefinement
