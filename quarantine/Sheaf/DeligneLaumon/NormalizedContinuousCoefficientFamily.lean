/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.DeligneLaumon.ContinuousConstructibleLatticeData

/-! # Normalized continuous coefficients at a fixed field -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped TensorProduct CategoryTheory.Obj CategoryTheory.Functor

namespace WeilConjectures.StratifiedContinuousLattices

local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0} X.ProEt

/-- Normalized coefficient charts, scalar comparisons and module encodings at one field.

Source: Bhatt--Scholze, Lemma 6.8.2, Proposition 6.8.4 and Remark 6.8.15;
steps 2, 4 and 5 of lem-zl-continuous-constructible-stratified-lattices.
(blueprint: lem-zl-normalized-continuous-coefficient-family).

Proof: the norm extending the l-adic norm is ultrametric, so E and its integral
subring are totally disconnected. The canonical condensed charts are therefore
isomorphisms. Identify the completed integral sheaf with continuous functions by
continuousCoefficientCompletion and its constant-preserving quotient isomorphisms;
the projection equations give integral_reduction. The continuous rational chart and
localization give rational, rational_values and localization_normalized. Naturality
in the integral inclusion gives inclusion_square. The section-action equivalence
retains the section groups and all maps, giving identity_sections and identity_maps.
Transport its scalar restriction identity and take its unit-normalized left-adjoint
comparison to obtain ScalarComparison, with the stated formula on tensor units.
The encoding local-freeness criterion supplies lisse. The exact monoidal inverse
image commutes with the section-action encoding: both use the pulled action followed
by extension along the continuous coefficient map. On the inverse-image unit this
comparison is the identity, giving restriction_unit. These constructions are made
for all X and both coefficient rings. Rank zero, varying ranks and empty covers are
allowed by the local-freeness criterion. No lattice is chosen in this step. -/
theorem normalized_continuous_coefficient_family (l : ℕ) [Fact l.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] : Nonempty (CoefficientFamily l E) := by sorry

end WeilConjectures.StratifiedContinuousLattices
