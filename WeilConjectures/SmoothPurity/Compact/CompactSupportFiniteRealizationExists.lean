/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Compact.CompactSupportFiniteRealizationPredicate

/-! # Existence for the existing compact-support realization predicate

Project the integral-functor conjunct of the existing representative comparison.
(blueprint: lem-weil-compact-support-finite-realization-exists).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

section FiniteAction
variable (l : ℕ) [Fact l.Prime]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

/-- The compact-support realization exists directly on condensed coefficient modules.
Source: blueprint latest, det-def-sf-operations, clause (iv)
(blueprint: lem-weil-compact-support-finite-realization-exists).

Proof: take the functor obtained by deriving exact extension by zero along the open
part and then deriving pushforward along the proper part of the compactification.
The identity natural isomorphism witnesses the realization predicate. This constructs
the functor directly and uses no existence theorem to choose its data. -/
theorem sfCompactSupportFiniteRealization
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    ∃ F, SfCompactSupportFiniteRealizationSpec Λ c F := by
  exact ⟨ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactification Λ c, ⟨Iso.refl _⟩⟩

end FiniteAction
end WeilConjectures
