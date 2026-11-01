/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPointDualComparisonData

/-! # Finite-model duality for condensed point evaluation -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsAlgClosed k]
  (I : Type w) [Finite I]

/--
The lax-monoidal internal-Hom comparison at the coefficient unit is invertible.
Source: the local boundary duality proof, Step 5 (finite free models and duality).

Proof: restrict to each component of the finite clopen boundary. Constructible cohomology
over an algebraically closed point is a finite sum of coefficient units. The unit is
projective, so split cohomology and obtain a bounded zero-differential complex of finite
free modules representing the restriction. Glue these complexes along the disjoint clopen
components. Apply the bounded-free ringed-site Hom model with target the coefficient unit:
its terms are the finite free duals in the opposite degrees, so the dual again has bounded
constructible cohomology. Restriction commutes with this Hom model because its source is
finite free. Sections carry each finite free dual to the ordinary finite free linear dual.
The projective Hom evaluation model computes the target derived Hom by that same complex.
The section tensor normalization identifies evaluation on homogeneous pure tensors; the
complex tensor normalization descends that identity, including the totalization signs.
Since the canonical comparison is the transpose of this evaluation, it is the isomorphism
between these two models. Transport along the representing quasi-isomorphisms finishes.
For the zero complex and an empty boundary all terms are zero and the same argument applies.
The comparison statement itself is pointwise in t, so no choice of component ordering is used.
(blueprint: lem-a1-condensed-point-duality-finite-model)
-/
theorem condensed_point_duality_finite_model
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    [s : CondensedBoundaryEvaluationTensor ℓ k I]
    (hs : IsCanonicalCondensedBoundaryEvaluationTensor ℓ k I) :
    ∀ (K : DerivedCategory (CondensedBoundaryMod ℓ k I)),
      constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ)
        (condensedPointBoundary k I) K →
      ∀ t : I, IsIso ((Functor.LaxMonoidal.ihomComparison
          (condensedBoundaryFiber ℓ k I t) K).natTrans.app (𝟙_ _)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
