/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearScalarOrdinaryInterface
import WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearScalarProperOpen
import Mathlib.CategoryTheory.Functor.OfSequence

/-! # Section-normalized ordinary scalar restriction

Source: Stacks Project, Tags 03CY, 03D7, 03D8, 03DA, 03DI, 03DJ and 0F7B.

The existence theorem below supplies one simultaneous package on the actual ordinary
semilinear-system and strict-tower categories. Every comparison has a section or
adjunction normalization. The constant-tower beta, projector and alpha in the package
are fixed by the same intrinsic ordinary words as their varying-ring counterparts.
No choice of a package is made into a definition.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.VaryingRing

variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)
  (B : Type (u + 1)) [CommRing B] (ψ : ∀ n : ℕ, CommRingCat.of B ⟶ R n)

/-- Ordinary scalar restriction and all its section-normalized comparisons exist.
Source: Stacks 03CY, 03D7, 03D8, 03DA, 03DI, 03DJ and 0F7B. -/
theorem ordinaryScalarComparison (hψ : ∀ n : ℕ, ψ (n + 1) ≫ φ n = ψ n) :
    Nonempty (OrdinaryScalarComparison R φ B ψ) := by
  obtain ⟨C⟩ := ordinaryScalarRestriction R φ B ψ hψ
  obtain ⟨G⟩ := ordinaryScalarAdjunctions R φ B ψ hψ C
  obtain ⟨P⟩ := ordinaryScalarProperOpen R φ B ψ hψ C G
  exact ⟨{
    rho := C.rho
    additive := C.additive
    limits := C.limits
    colimits := C.colimits
    level := C.level
    level_sections := C.level_sections
    transitions := C.transitions
    b := G.b
    d := G.d
    d_sections := G.d_sections
    unit := OrdinaryScalarAdjunctions.unit R φ B ψ C G
    counit := OrdinaryScalarAdjunctions.counit R φ B ψ C G
    mate := G.mate
    a := G.a
    open_unit := G.open_unit
    beta := P.beta
    beta_unit := P.beta_unit
    beta_comparison := P.beta_comparison
    clopen := P.clopen
    clopen_unit := P.clopen_unit
    pi := scalarOrdinaryPi B P.clopen
    pi_eq := by intros; rfl
    pi_comparison := P.pi_comparison
    alpha := P.alpha
    alpha_eq := P.alpha_eq
    alpha_comparison := P.alpha_comparison }⟩

end AlgebraicGeometry.ProEtale.VaryingRing
