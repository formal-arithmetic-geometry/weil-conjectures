/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Compact.CompactSupportRepresentativeIndependence

/-! # The existing compact-support realization predicate

This module defines the predicate recording a strict-tower realization of the compact-support
integral functor.

## Implementation details

The predicate lives in its own module to avoid repeated checking of its large choice telescope
while compiling the finite-action constructions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  completedIntegralCoefficientSheafUnrestricted
  constantSheaf
  sfIntegralCompactSupportValue
  Padic.coefficientExtensionIdeal

section FiniteAction
variable (l : ℕ) [Fact l.Prime]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

/-- The predicate that an integral functor is the strict-tower realization, retaining the chosen
tower, derived limit and projection normalizations. -/
def SfCompactSupportFiniteRealizationSpec
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    (sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E Y) → Prop :=
  (fun {P : (sfIntegralConstructibleCategory l E X ⥤
      sfIntegralConstructibleCategory l E Y) → Prop} (_h : ∃ F, P F) ↦ P)
    ((exists_compactSupportRepresentativeComparison l
      E K₀ hl X Y f c).choose_spec.choose_spec.2.2.choose_spec.choose_spec
        |>.2.2.choose_spec.2)

end FiniteAction
end WeilConjectures
