/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsBasis
public import Submission.WeilConjectures.CategoryTheory.ModuleObjects.Free
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.SubfieldBasis

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# `F_X` is finite free over `E_X`

For finite subextensions `E ≤ F` of `ℚ̄_ℓ / ℚ_ℓ` and a scheme `X`, the coefficient ring `F_X`,
regarded as an `E_X`-module through the inclusion `E_X ⟶ F_X`, is finite free
(blueprint `sk-prop-sfb-cartesian-coefficients` (2)), of rank `[F : E]`: an `E`-basis `eᵢ` of
`F` gives an isomorphism `E_X^{⊕ [F : E]} ⟶ F_X`, `(aᵢ) ↦ ∑ aᵢ eᵢ`
(`AlgebraicGeometry.ProEtale.isIso_biproductDesc_padicSubfieldBasisSection`), which is
`E_X`-linear (`CategoryTheory.Mod.isIso_biproductDesc_basisHom`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace AlgebraicGeometry.ProEtale.CondensedRing

open PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] {E F : FiniteIntermediateField ℓ} (h : E ≤ F)

/-- Blueprint `sk-prop-sfb-cartesian-coefficients` (2): for finite subextensions `E ≤ F`, the
coefficient ring `F_X`, regarded as an `E_X`-module, is finite free, of a rank independent of
the scheme `X`. -/
theorem exists_comap_regular_iso_finiteFree :
    ∃ d : ℕ, ∀ X : Scheme.{u},
      Nonempty ((Mod.comap (padicSubfieldRingObjMap X ℓ h)).obj
          (Mod.regular (padicSubfieldRingObj X ℓ F)) ≅
        Mod.finiteFree (padicSubfieldRingObj X ℓ E) d) := by
  refine ⟨FiniteIntermediateField.finrankOfLE h, fun X ↦ ⟨?_⟩⟩
  have := Mod.isIso_biproductDesc_basisHom (padicSubfieldRingObjMap X ℓ h)
    (padicSubfieldBasisSection X h) (isIso_biproductDesc_padicSubfieldBasisSection X h)
  exact (asIso (biproduct.desc fun i ↦
    Mod.basisHom (padicSubfieldRingObjMap X ℓ h) (padicSubfieldBasisSection X h i))).symm

end AlgebraicGeometry.ProEtale.CondensedRing
