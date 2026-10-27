/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Paper.ReconstructedPairRefinementData

/-! # Reconstructed RefinementTraceTransport

Source: blueprint sk-prop-sp-unique-adjoint, categorical proof, and
sk-thm-purity-transport Steps 2--4
(blueprint: lem-pur-reconstructed-refinement-trace-transport).
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

/-- The integral refinement counit equation transports through all three coefficient
realizations, for arbitrary integral objects and traces.
Source: blueprint sk-prop-sp-unique-adjoint categorical proof, Naturality;
sk-prop-sp-rational and sk-thm-sp-qbar; parent proof Steps 7--8.
Proof: apply the specified completed integral scalar extension to the input equality.
Naturality of its compact-support comparison and the coefficient refinement square
rewrite the image as the scalar equation. For rational realization apply the
rationalization/realization functor, use naturality of the specified realization
comparison, and invert its refinement square. For closure realization apply the
actual finite-valued closure scalar functor to the rational equality. Naturality
of the compact-support projection and condensedProjection_refinement identify the
inverse projection factors; all are invertible on bounded constructibles. Cancel
the inverse refinement and projection factors to obtain the closure equation.
All equalities are preserved by functors, so this works for arbitrary traces and
arbitrary integral morphisms; no representing-pair or theta hypothesis is needed.
(blueprint: lem-pur-reconstructed-refinement-trace-transport). -/
theorem reconstructedRefinementTraceTransport
    {c d : Compactification f} (w : c.Refinement d)
    (M₁ M₂ : CondensedERealization.Integral l E X.scheme)
    (L : CondensedERealization.Integral l E Y.scheme) (a : M₂ ⟶ M₁)
    (t₁ : (support l E k C X Y f c).obj M₁ ⟶ L)
    (t₂ : (support l E k C X Y f d).obj M₂ ⟶ L)
    (h : (support l E k C X Y f c).map a ≫ t₁ =
      (comparison l E k C X Y f w).hom.app M₂ ≫ t₂) :
    (∀ (H : Type u) [NormedField H] [NormedAlgebra ℚ_[l] H]
      [FiniteDimensional ℚ_[l] H] (i : E →ₐ[ℚ_[l]] H),
      (support l H k C X Y f c).map ((integralScalar l E H i k X).map a) ≫
          scalarTrace l E k C X Y f H i c t₁ =
        (comparison l H k C X Y f w).hom.app ((integralScalar l E H i k X).obj M₂) ≫
          scalarTrace l E k C X Y f H i d t₂) ∧
    ((fieldSupport l E k C X Y f c).map ((realize l E k C X).map a) ≫
        fieldTrace l E k C X Y f c t₁ =
      (fieldComparison l E k C X Y f w).hom.app ((realize l E k C X).obj M₂) ≫
        fieldTrace l E k C X Y f d t₂) ∧
    (∀ b : E →ₐ[ℚ_[l]] PadicAlgCl l,
      (omegaSupport l k X Y f c).map
          (((realize l E k C X) ⋙ toOmega l E k b X).map a) ≫
        omegaTrace l E k C X Y f b c (fieldTrace l E k C X Y f c t₁) =
      (omegaComparison l k X Y f w).hom.app
          (((realize l E k C X) ⋙ toOmega l E k b X).obj M₂) ≫
        omegaTrace l E k C X Y f b d (fieldTrace l E k C X Y f d t₂)) := by sorry

end WeilConjectures.ReconstructedPairRefinement
