/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ToPadicAlgClCompatibility

/-!

# The extension of scalars `E ⟶ ℚ̄_ℓ` is additive

The derived extension of scalars `ℚ̄_ℓ ⊗ᴸ_E - : D(Mod_{E_X}) ⥤ D(Mod_{ℚ̄_ℓ,X})` is additive, being a
left adjoint (`ProEtale.additive_derivedExtendScalarsToPadicAlgCl`), and so are its restrictions
`T_X : Dᵇc(X)⟦E⟧ ⥤ Dᵇc(X)⟦ℚ̄_ℓ⟧` to the bounded constructible complexes
(`ProEtale.CondensedRing.additive_boundedConstructibleToPadicAlgCl`,
`ProEtale.additive_constructibleToPadicAlgCl`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- The derived extension of scalars `ℚ̄_ℓ ⊗ᴸ_E -` is additive, being a left adjoint. -/
instance additive_derivedExtendScalarsToPadicAlgCl :
    (derivedExtendScalarsToPadicAlgCl X ℓ E).Additive := by
  -- the commutativity instances are given explicitly: the search goes through another braiding
  have adj := @Mod.derivedExtendMapDerivedCategoryAdjunction _ _ _ _ _ _ _ _ _ _ _ _ _
    (isCommMonObj_condensedRingObj _ X) (isCommMonObj_condensedRingObj _ X)
    (padicSubfieldRingObjToPadicAlgCl X ℓ E) _
  have : PreservesColimitsOfSize.{0, 0} (derivedExtendScalarsToPadicAlgCl X ℓ E) :=
    adj.leftAdjoint_preservesColimits
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (derivedExtendScalarsToPadicAlgCl X ℓ E)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- The extension of scalars `ℚ̄_ℓ ⊗ᴸ_E -` on bounded constructible complexes is additive. -/
instance additive_constructibleToPadicAlgCl : (constructibleToPadicAlgCl X ℓ E).Additive := by
  have : (constructibleToPadicAlgCl X ℓ E ⋙ (boundedConstructible _).ι).Additive :=
    inferInstanceAs ((boundedConstructible _).ι ⋙ derivedExtendScalarsToPadicAlgCl X ℓ E).Additive
  exact Functor.additive_of_comp_faithful _ (boundedConstructible _).ι

/-- The extension of scalars `ℚ̄_ℓ ⊗ᴸ_E -` on bounded constructible complexes is additive. -/
instance CondensedRing.additive_boundedConstructibleToPadicAlgCl :
    (CondensedRing.boundedConstructibleToPadicAlgCl X ℓ E).Additive :=
  inferInstanceAs (constructibleToPadicAlgCl X ℓ E).Additive

end AlgebraicGeometry.ProEtale
