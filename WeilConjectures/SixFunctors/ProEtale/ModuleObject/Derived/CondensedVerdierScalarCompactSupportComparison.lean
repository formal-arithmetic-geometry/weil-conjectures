/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedVerdierScalarTransport
public import WeilConjectures.Compactification.BoundaryRefinement
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.SixFunctors.ShriekCoefficientIsomorphism

/-! # Compact support commutes with derived scalar extension along an isomorphism -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped MonoidalCategory CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing

local instance scalarSupportSmall (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

/-- The compact-support square for the actual derived extension scalar transport.
Source: blueprint coefficient normalization, compact-support comparison in paragraph (i).
(blueprint: lem-sf-condensed-verdier-scalar-compact-support-comparison).

Proof: identify scalar extension with derived restriction along the inverse coefficient
isomorphism on the source and target. Whisker the target identification with compact
support, use shriekCoefficientCompactificationIso for derived restriction, then whisker
the inverse source identification with normalized compact support. Compose these three
natural isomorphisms. No adjunction or constructible preservation is assumed here. -/
theorem condensedVerdier_scalar_compact_support_comparison
    {Λ Γ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Γ] [IsCommMonObj Γ]
    (e : Mon.mk Λ ≅ Mon.mk Γ) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification.BoundaryCompactification f) :
    Nonempty (rightDerivedLowerShriekOfCompactification Λ c.obj.obj ⋙
        condensedVerdierScalarTransport e Y ≅
      condensedVerdierScalarTransport e X ⋙
        rightDerivedLowerShriekOfCompactification Γ c.obj.obj) := by
  obtain ⟨sX⟩ := (condensedVerdier_scalar_constructible_equivalence e X).1
  obtain ⟨sY⟩ := (condensedVerdier_scalar_constructible_equivalence e Y).1
  exact ⟨Functor.isoWhiskerLeft _ sY ≪≫
    shriekCoefficientCompactificationIso e c ≪≫
    Functor.isoWhiskerRight sX.symm _⟩

end AlgebraicGeometry.ProEtale.CondensedRing
