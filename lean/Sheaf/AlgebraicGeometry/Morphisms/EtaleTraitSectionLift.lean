/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! Etale local trait lifts of sections. -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A pointed etale neighbourhood of a trait section supplies an unramified trait lift.

Source: Stacks Project, Tag 0EYI, preliminary paragraph; Tag 0AP2 (15.45.4).
(blueprint: lem-sbc-etale-trait-section-lift)

Proof: Form Spec B times_L Spec R and choose a point above y and the closed point
using a common extension of their residue fields. Take its local ring A. The
projection to Spec B induces iota and that to Spec R induces delta. The projection
to the trait is etale; its local ring at this point is a DVR, and the local map
delta is flat and injective. Its closed fibre is a field, so the maximal ideal of
A is the extension of the maximal ideal of R. Thus delta(varpi0) generates it.
The equality phi followed by p = Spec rho and the pullback square give both the
commuting scheme maps and iota(rho(varpi0)) = delta(varpi0). These witnesses are
used only in the existential proof, never to define an unspecified object. -/
theorem etale_trait_section_lift (R : CommRingCat.{u})
    [IsDomain R] [IsDiscreteValuationRing R]
    {L : Scheme.{u}} (p : L ⟶ Spec R) (τ : Spec R ⟶ L) (hτ : τ ≫ p = 𝟙 _)
    (B : CommRingCat.{u}) (φ : Spec B ⟶ L) (y : Spec B) (hφ : Etale φ)
    (hy : φ y = τ (IsLocalRing.closedPoint R))
    (ρ : R →+* B) (hρ : φ ≫ p = Spec.map (CommRingCat.ofHom ρ))
    (ϖ₀ : R) (hϖ₀ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ₀}) :
    ∃ (A : CommRingCat.{u}) (_ : IsDomain A) (_ : IsDiscreteValuationRing A)
      (δ : R →+* A) (ι : B →+* A),
      Function.Injective δ ∧
      IsLocalRing.maximalIdeal A = Ideal.span {δ ϖ₀} ∧
      ι (ρ ϖ₀) = δ ϖ₀ ∧
      Spec.map (CommRingCat.ofHom ι) ≫ φ =
        Spec.map (CommRingCat.ofHom δ) ≫ τ := by sorry


end AlgebraicGeometry.Scheme
