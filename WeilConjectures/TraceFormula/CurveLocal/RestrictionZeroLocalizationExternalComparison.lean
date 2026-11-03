/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.CurveLocal.ModelVanishing
public import WeilConjectures.TraceFormula.CurveLocal.FrobeniusModel
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.Compactification.NagataCompactification

/-! The external-product localization comparison used by
`det-tf-restriction-zero-localization`.

Source: literature/blueprint/latest/blueprint/sec-trace-formula/
sk-lem-tf-curve-restriction-zero/det-tf-restriction-zero-localization.md, clause (i)
(blueprint: restriction-zero-localization-external-comparison).

The proof is ordinary Künneth, extension-by-zero base change, and strict-localization continuity.
This is independent of the Verdier-dual direct-image comparison above.
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

abbrev restrictionZeroLocalizationTwoAxesOpen (M : CurveLocalModel k) : M.T.Opens :=
  M.hH.openComplement ⊓ M.v.openComplement

abbrev restrictionZeroLocalizationTwoAxesInclusion (M : CurveLocalModel k) :
    (restrictionZeroLocalizationTwoAxesOpen M).toScheme ⟶ M.v.openComplement.toScheme :=
  M.T.homOfLE inf_le_right

/-- Clause (i), external-product/extension comparison on the strict-local model.

The source proof combines ordinary Künneth with arbitrary-base-change for open extension and the
continuity theorem for strict localization.  No imported declaration packages this composite
comparison; it is the second independent geometric obligation (estimated at more than four hours
because all three mate and continuity squares must be assembled).
(blueprint: restriction-zero-localization-external-comparison). -/
theorem restrictionZeroLocalization_externalComparison
    {Λ : Type (u + 1)} [CommRing Λ]
    (M : CurveLocalModel k)
    (L K : DerivedCategory (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (P : DerivedCategory.Plus
      (Sheaf M.T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (eP : P.obj ≅ D((M.τ)^*[ModuleCat.{u + 1} Λ]).obj
      (externalProduct (ModuleCat.{u + 1} Λ) M.f M.f L K)) :
    Nonempty (P.obj ≅
      (R((M.v.openComplement.ι)_*[ModuleCat.{u + 1} Λ])).obj
        (D((restrictionZeroLocalizationTwoAxesInclusion M)_!open[ModuleCat.{u + 1} Λ]).obj
          (D(((restrictionZeroLocalizationTwoAxesOpen M).ι)^*[ModuleCat.{u + 1} Λ]).obj
            (D((M.τ)^*[ModuleCat.{u + 1} Λ]).obj
              (externalProduct (ModuleCat.{u + 1} Λ) M.f M.f L K))))) := by
  sorry

end AlgebraicGeometry.Etale.CurveLocalModel
