/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Paper.ReconstructedPairRefinementData

/-! # Reconstructed RefinementCommon

Source: blueprint sk-prop-sp-unique-adjoint, categorical proof, and
sk-thm-purity-transport Steps 2--4
(blueprint: lem-pur-reconstructed-refinement-common).
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

/-- Common-refinement independence in system and reconstructed integral coordinates.
Source: Stacks Tags 0ATU and 0F7C--0F7J; parent proof Steps 2--3.
Proof: take a further compactification dominating the two chosen common refinements,
and equalize the two parallel arrows to each endpoint. For intrinsic system support,
composition factors each refined downward arrow through the same further-refinement
arrow. Its component is invertible on the bounded-below etale-origin input by finite
proper/open calculus and conservative evaluations. Cancel that common factor to
identify the ratios. Coordinate conjugation cancels its intermediate beta and
coordinate counit factors, so the same equality holds for systemCommon even when
the Brown packages at the two dominating objects differ. Applying actual total limit
and restricting to complete objects gives integral commonComparison independence.
No equality is detected merely from finite evaluations.
(blueprint: lem-pur-reconstructed-refinement-common). -/
theorem reconstructedRefinementCommon :
    (∀ (c d e e' : Compactification f)
    (D₁ : At l E k C X Y f c) (D₂ : At l E k C X Y f d)
    (D₀ : At l E k C X Y f e) (D₀' : At l E k C X Y f e')
    (r : e.Refinement c) (s : e.Refinement d)
    (r' : e'.Refinement c) (s' : e'.Refinement d)
    (B : DerivedCategory (BrownTowerComparison.ProSystem X.scheme
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)))
    (hB : D₀.transport.siteX.Origin B) (hB' : D₀'.transport.siteX.Origin B),
    systemCommon D₁ D₂ D₀ r s B hB = systemCommon D₁ D₂ D₀' r' s' B hB') ∧
    (∀ (c d e e' : Compactification f)
    (r : e.Refinement c) (s : e.Refinement d)
    (r' : e'.Refinement c) (s' : e'.Refinement d),
    commonComparison l E k C X Y f r s = commonComparison l E k C X Y f r' s') := by sorry

end WeilConjectures.ReconstructedPairRefinement
