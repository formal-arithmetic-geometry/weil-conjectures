/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Field.ZMod
public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
public import WeilConjectures.ConstructibleSheaf.Defs

import WeilConjectures.AlgebraicGeometry.FiniteEtaleModuleTraceDegree
import Mathlib.Algebra.Field.ZMod

/-!
# Finite étale trace splitting

Source: Stacks Project, etale-cohomology.tex, Section 03SH, Definition 03SE.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Etale

/-- **The adjunction unit splits for a prime-to-ℓ finite étale cover.**
The coefficient field is `ULift.{u + 1} (ZMod ℓ)`, a universe lift of the prime field
`ℤ/ℓℤ`.

Source: Stacks Project, `etale-cohomology.tex`, Section 03SH, the characterization and
restriction/trace composite immediately after Definition 03SE. -/
theorem Scheme.IsFiniteLocallyConstantSheaf.exists_finite_etale_retraction
    {U V : Scheme.{u}} (ℓ : ℕ) [Fact ℓ.Prime]
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    [IsFiniteLocallyConstantSheaf G] (v : V ⟶ U) [IsFinite v] [Etale v]
    [ConnectedSpace V] (d : ℕ) (hd : ¬ ℓ ∣ d)
    (hdeg : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U),
      Nat.card (v.GeometricFiber s) = d) :
    ∃ r : (v)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj
          ((v)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj G) ⟶ G,
        (Etale.upperStarLowerStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) v).unit.app G ≫ r = 𝟙 G := by
  obtain ⟨t, ht⟩ := exists_finiteEtaleModuleTrace_degree
    (ULift.{u + 1} (ZMod ℓ)) v G d hdeg
  have hd0 : (d : ZMod ℓ) ≠ 0 := (ZMod.natCast_eq_zero_iff d ℓ).not.mpr hd
  refine ⟨(d : ULift.{u + 1} (ZMod ℓ))⁻¹ • t, ?_⟩
  rw [Linear.comp_smul, ht, smul_smul]
  have hi : (d : ULift.{u + 1} (ZMod ℓ))⁻¹ * (d : ULift.{u + 1} (ZMod ℓ)) = 1 := by
    apply ULift.ext
    change (d : ZMod ℓ)⁻¹ * (d : ZMod ℓ) = 1
    exact inv_mul_cancel₀ (a := (d : ZMod ℓ)) hd0
  rw [hi, one_smul]

end AlgebraicGeometry
