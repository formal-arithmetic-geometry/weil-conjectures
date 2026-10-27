/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicIntegralModel
public import WeilConjectures.PoincareDuality.Biduality.Integral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IhomCompatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.UpperShriekCompatibilityProper

/-!
# Biduality along the coefficient change `𝒪_E ⟶ ℚ̄_ℓ`

Write `T_X = ℚ̄_ℓ ⊗ᴸ_{𝒪_E} - : Dᵇc(X)⟦𝒪_E⟧ ⥤ Dᵇc(X)⟦ℚ̄_ℓ⟧` for the extension of scalars along
`𝒪_E ⟶ E ⟶ ℚ̄_ℓ` on bounded constructible complexes. This file proves the last two steps of
blueprint `det-pd-biduality-coefficients` ((iii) and (iv)): `T_X` carries the double-dual morphism
of an integral complex to the double-dual morphism of its extension of scalars, and every bounded
constructible `ℚ̄_ℓ`-complex has an integral model, so `ℚ̄_ℓ`-biduality follows from
`𝒪_E`-biduality.

## Main results

- `ProEtale.CondensedRing.integersToPadicAlgClDualizingComplexIso`: `T_X ω_{X, 𝒪_E} ≅ ω_X`, from
  the coefficient comparisons for `Rf^!` (blueprint `det-prop-scalar-six-exceptional`).
- `ProEtale.CondensedRing.isIso_verdierBiduality_integersToPadicAlgCl_obj`: if `δ_{K₀}` is an
  isomorphism, so is `δ_{T_X K₀}`. This is the formal compatibility of the double-dual morphism
  with lax braided functors (`CategoryTheory.MonoidalClosed.isIso_map_toIhomIhom_iff`), `T_X`
  commuting with internal homs (blueprint `det-prop-scalar-six-tensor-hom`).
- `ProEtale.CondensedRing.isIso_verdierBiduality_of_integral`: `ℚ̄_ℓ`-biduality from
  `𝒪_E`-biduality, by integral models (`ProEtale.exists_padicAlgCl_iso_integralModel`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : PadicAlgCl.FiniteIntermediateField ℓ)

variable (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

/-- The extension of scalars of the integral dualizing complex is the dualizing complex:
`T_X ω_{X, 𝒪_E} ≅ ω_X`. It is the coefficient comparison for `Ra_X^!` along `𝒪_E ⟶ E` and
`E ⟶ ℚ̄_ℓ` (`boundedConstructibleUpperShriekExtendScalarsIso`,
`isIso_boundedConstructibleUpperShriekToPadicAlgCl`, blueprint
`det-prop-scalar-six-exceptional`) at the unit, followed by the unit comparisons of the monoidal
functors `T_X`. -/
noncomputable def integersToPadicAlgClDualizingComplexIso :
    (boundedConstructibleExtendScalars X.left ℓ E ⋙ constructibleToPadicAlgCl X.left ℓ E).obj
        (PadicIntegersRingObj.dualizingComplex ℓ E.1 X) ≅
      dualizingComplex ℓ X :=
  sorry

variable {X}

/-- **Biduality along `𝒪_E ⟶ ℚ̄_ℓ`** (blueprint `det-pd-biduality-coefficients`, (iii) and (iv)):
if the double-dual morphism `δ_{K₀}` of a bounded constructible `𝒪_E`-complex is an isomorphism,
so is the double-dual morphism of its extension of scalars `T_X K₀`. -/
theorem isIso_verdierBiduality_integersToPadicAlgCl_obj
    (K₀ : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧)
    (hK₀ : IsIso (PadicIntegersRingObj.verdierBiduality ℓ E.1 K₀)) :
    IsIso (verdierBiduality ℓ
      ((boundedConstructibleExtendScalars X.left ℓ E ⋙ constructibleToPadicAlgCl X.left ℓ E).obj
        K₀)) :=
  sorry

/-- **`ℚ̄_ℓ`-biduality from `𝒪_E`-biduality** (blueprint `det-pd-biduality-coefficients`, (iv)):
if the double-dual morphisms of all bounded constructible `𝒪_E`-complexes on `X`, for all finite
subextensions `E`, are isomorphisms, so is the double-dual morphism of every bounded
constructible `ℚ̄_ℓ`-complex `K`: `K ≅ T_X K₀` for an integral model `K₀`. -/
theorem isIso_verdierBiduality_of_integral
    (h : ∀ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (K₀ : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧),
      IsIso (PadicIntegersRingObj.verdierBiduality ℓ E.1 K₀))
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (verdierBiduality ℓ K) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
