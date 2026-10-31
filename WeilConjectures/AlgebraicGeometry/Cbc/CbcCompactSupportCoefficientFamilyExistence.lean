/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Normalized.NormalizedCoefficientFamilies

/-! # Normalized compact-support families

Source: current blueprint, compact-support scalar comparison.
(blueprint: lem-cbc-normalized-support-family-existence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
  [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
  [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]

/-- The normalized compact-support family exists for each chosen compactification.
This concerns one operation, with no base-change square or exchange.

Source: current blueprint, coefficient coherence of units and counits;
lem-cbc-rational-compact-support-coefficient-coherence, steps 1--4, 14, 16.
(blueprint: lem-cbc-normalized-support-family-existence).

Proof: restrict the actual Rp_* j_! using integral compact-support uniform
restriction. Its exactness and constant-section linearity allow raw rational
transport. Finite free completed coefficient extension is ordinary derived
tensor. On extension-by-zero summands its comparison sends
(i_alpha x) tensor s to i_alpha(x tensor s); the ringed-slice tensor identity
makes this an isomorphism of modules over the larger ring. It agrees with the
inverse open-unit mate, by the adjunction unit characterization. Compose it
with the canonical proper counit-tensor comparison. The resulting inverse is
exactly cbcScalarCompactSupportInverse. Tensor units give the identity case.
For three fields, both open maps send ((i_alpha x) tensor s) tensor z to
 i_alpha(x tensor sz); the proper comparison has the same associator law.
Naturality moves the inner open map past the proper comparison and cancels
adjacent associators, proving stage-system coherence. All degreewise maps
commute with shifts. Localizing these equations gives betaCommShift and the
specified beta components; exact rational transport gives stage exactness.
Localization changes neither objects nor the actual integral maps, giving the
localization and shift specifications. The repeated-field tensor unit gives
the required literal unit normalization. -/
theorem cbcCompactSupportCoefficientFamily_exists {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f) :
    Nonempty (CbcCompactSupportCoefficientFamily l Ω c) := by
  sorry

end AlgebraicGeometry.Scheme
