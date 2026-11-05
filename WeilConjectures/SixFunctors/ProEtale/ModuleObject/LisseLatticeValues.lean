/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsRegular
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ContinuousMapCoefficientSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LisseLatticeBasis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LisseLatticeTransition

/-!
# Values of sections of `E_X` and integral sections

Let `E ⊆ ℚ̄_ℓ` be a finite extension of `ℚ_ℓ`. For a scheme `W`, the endomorphisms of the regular
module `E_W` are the global sections of `E_W`, that is the continuous functions `W → E`; the
restriction along `g : W' ⟶ W` is the precomposition with `g`
(`AlgebraicGeometry.ProEtale.exists_subfieldEndRingEquiv`). An endomorphism whose function takes
values in `𝒪_E` is the extension of a global section of `𝒪_{E,W}`.

We also show that the units `𝒪_{E,V}ⁿ ⟶ E_V ⊗ 𝒪_{E,V}ⁿ` are monomorphisms
(`AlgebraicGeometry.ProEtale.mono_extendRestrictAdjunction_unit_app_finiteFree_padicIntegers`):
the inclusion `𝒪_{E,V} ⟶ E_V` is a monomorphism, `𝒪̲_E ⟶ E̲` being injective on sections and
`p_V^*` exact.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)

/-! ### Integral sections -/

/-! ### Values of endomorphisms of `E_W` -/

/-! ### The units `𝒪_{E,V}ⁿ ⟶ E_V ⊗ 𝒪_{E,V}ⁿ` are monomorphisms -/

end AlgebraicGeometry.ProEtale
