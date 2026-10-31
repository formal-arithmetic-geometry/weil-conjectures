/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurIntegralSupportComparison.PurIntegralSupportComparisonData

/-! Uniqueness of normalized ordinary quotient-coordinate comparisons.

Source: Zheng Construction 4.1 and Lemma 4.10; blueprint
lem-route-ordinary-exists-unique, uniqueness step.
(blueprint: lem-route-ordinary-uniqueness)

The two normalized direct-image fields are determined sectionwise by cancellation
of the right-underlying comparison. The transpose equations and injectivity of the
four adjunction hom bijections then determine the inverse and extension fields;
proof irrelevance identifies the remaining normalization proofs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SheafOfModules Opposite
open WeilConjectures AlgebraicGeometry.Scheme
namespace WeilConjectures.PurIntegralSupportComparison

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  (S : StrictEtaleCompactSupport (integralExceptionalIntegers l E)
    (integralExceptionalUniformizer l E) c)
  (G : EtaleTowerBrownAdjunction S) (H : BrownTowerComparison.FiniteEvaluation S G)
  (D : BrownTowerComparison.TransportData S G H)

/-- Any two normalized ordinary comparison records are equal.
Source: Zheng Construction 4.1 and the paragraph before Lemma 4.10;
uniqueness steps of lem-route-ordinary-exists-unique.
(blueprint: lem-route-ordinary-uniqueness)

Proof: the normalization equations for openPush and properPush identify their
section functions after postcomposition with rightEvaluation and rightUnderlying.
Both postcomposed maps are isomorphisms, hence injective on sections. Cancel them
and apply extensionality successively to module-sheaf maps, strict-system maps,
natural transformations and isomorphisms. The push fields agree.

In openPull_transpose take N to be the sequence inverse-image object of M and h
to be its identity. Both right sides now agree. Injectivity of the ordinary Hom
adjunction, followed by natural-isomorphism extensionality, identifies openPull.
In openExtension_transpose take N to be the sequence extension object of M and h
to be its identity. Cancel the already identified openPull component, and apply
injectivity of the extension Hom adjunction to identify openExtension. All
remaining record fields are propositions, so proof irrelevance identifies the
records. No existence of a record or nonempty-scheme hypothesis is used. -/
theorem ordinary_unique (B B' : Ordinary l E S G H D) : B = B' := by
  sorry

end WeilConjectures.PurIntegralSupportComparison
