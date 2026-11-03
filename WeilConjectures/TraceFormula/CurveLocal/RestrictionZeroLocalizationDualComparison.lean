/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.CurveLocal.ModelVanishing
public import WeilConjectures.TraceFormula.CurveLocal.FrobeniusModel
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing

/-! The Verdier-dual localization comparison used by
`det-tf-restriction-zero-localization`.

Source: literature/blueprint/latest/blueprint/sec-trace-formula/
sk-lem-tf-curve-restriction-zero/det-tf-restriction-zero-localization.md, clause (i)
(blueprint: restriction-zero-localization-dual-comparison).

The proof is the open-immersion internal-Hom adjunction followed by the strict-localization
continuity comparison.  Those two comparisons are independent of the localization triangle and
are deliberately isolated here for the next proof pass.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.CurveLocalModel

open Scheme

variable {k : Type u} [Field k] [IsAlgClosed k]

local instance (M : CurveLocalModel k) : IsClosedImmersion M.y :=
  isClosedImmersion_of_comp_eq_id M.f M.y M.y_comp

/-- Clause (i), dual direct-image comparison on the strict localization.

The source proof is the open-closed internal-Hom calculation for `K = j_!Q`, followed by the
stalkwise strict-localization continuity theorem.  The latter comparison is not yet packaged in
the imported source modules; this is the first of the two independent geometric obligations
(estimated at more than four hours of work because it requires the full continuity and duality
mate calculation).
(blueprint: restriction-zero-localization-dual-comparison). -/
theorem restrictionZeroLocalization_dualComparison
    {Λ : Type (u + 1)} [CommRing Λ]
    (M : CurveLocalModel k)
    (L K : DerivedCategory (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    let c := strictLocalizationToBase M.y
    let j := (strictLocalizationToBase M.y ⁻¹ᵁ M.y.openComplement).ι
    let Lloc := D((c)^*[ModuleCat.{u + 1} Λ]).obj L
    let N := D((j)^*[ModuleCat.{u + 1} Λ]).obj Lloc
    Nonempty (Lloc ≅ (R((j)_*[ModuleCat.{u + 1} Λ])).obj N) := by
  sorry

end AlgebraicGeometry.Etale.CurveLocalModel
