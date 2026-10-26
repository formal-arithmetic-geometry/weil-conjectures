/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicSubfieldFinite
public import WeilConjectures.TraceFormula.ExternalProductExtendScalars

/-!
# Extension of scalars `𝒪_E ⟶ ℚ̄_ℓ`, pushforward and extension by zero

Write `T_X = ℚ̄_ℓ ⊗ᴸ_{𝒪_E} - : Dᵇc(X)⟦𝒪_E⟧ ⥤ Dᵇc(X)⟦ℚ̄_ℓ⟧`
(`ProEtale.CondensedRing.boundedConstructibleIntegersToPadicAlgCl`). This file proves that `T`
commutes with the pushforward along any morphism of separated `k`-schemes of finite type
(`ProEtale.CondensedRing.boundedConstructibleLowerStarIntegersToPadicAlgClIso`, blueprint
`det-prop-scalar-six-direct-image` for `𝒪_E ⟶ ℚ̄_ℓ`) and with the extension by zero along an open
immersion (`ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekIntegersToPadicAlgClIso`),
and that bounded constructible `ℚ̄_ℓ`-complexes on two schemes have integral models over a common
`𝒪_E` (`ProEtale.exists_padicAlgCl_iso_integralModel_pair`).

The comparison for the pushforward is the composite of the ones for `𝒪_E ⟶ E`
(`ProEtale.CondensedRing.boundedConstructibleLowerStarExtendScalarsIso`) and for `E ⟶ ℚ̄_ℓ`. The
latter is the restriction of the derived comparison **(Push)**
`ℚ̄_ℓ ⊗ᴸ_E Rf_* K ⟶ Rf_* (ℚ̄_ℓ ⊗ᴸ_E K)`, which is an isomorphism on bounded below objects
(`ProEtale.CondensedRing.isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

/-- **Integral models over a common `𝒪_E`**: bounded constructible `ℚ̄_ℓ`-complexes `K` on `X` and
`K'` on `X'` (topologically noetherian schemes) are isomorphic to `ℚ̄_ℓ ⊗ᴸ_{𝒪_E} K₀` and
`ℚ̄_ℓ ⊗ᴸ_{𝒪_E} K₀'` for one finite subextension `E` and bounded constructible `𝒪_E`-complexes
`K₀`, `K₀'` (blueprints `sk-thm-sfb-qlbar-two-colimit` and `sk-lem-tf-rational-model`): both
descend to finite subextensions, hence to a common one containing both, where they have
integral models. -/
lemma exists_padicAlgCl_iso_integralModel_pair (X X' : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [TopologicalSpace.NoetherianSpace X] [TopologicalSpace.NoetherianSpace X']
    (K : PadicAlgClConstructible X ℓ) (K' : PadicAlgClConstructible X' ℓ) :
    ∃ (E : FiniteIntermediateField ℓ)
      (K₀ : BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))
      (K₀' : BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X')),
      Nonempty ((constructibleToPadicAlgCl X ℓ E).obj
        ((boundedConstructibleExtendScalars X ℓ E).obj K₀) ≅ K) ∧
      Nonempty ((constructibleToPadicAlgCl X' ℓ E).obj
        ((boundedConstructibleExtendScalars X' ℓ E).obj K₀') ≅ K') :=
  sorry

namespace CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

section LowerStar

variable {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- **(Push)** on bounded constructible complexes for `𝒪_E ⟶ ℚ̄_ℓ` (blueprint
`det-prop-scalar-six-direct-image`), for any morphism `g` of separated `k`-schemes of finite type:
`Rg_*^{𝒪_E} ⋙ T_Y ≅ T_Z ⋙ Rg_*^{ℚ̄_ℓ}`. It is the comparison for `𝒪_E ⟶ E`
(`boundedConstructibleLowerStarExtendScalarsIso`) followed by the one for `E ⟶ ℚ̄_ℓ`, the
restriction of the derived (Push), which is invertible on bounded below objects
(`isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE`). -/
noncomputable def boundedConstructibleLowerStarIntegersToPadicAlgClIso (g : Z ⟶ Y) :
    PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E.1 g ⋙
        boundedConstructibleIntegersToPadicAlgCl ℓ E Y ≅
      boundedConstructibleIntegersToPadicAlgCl ℓ E Z ⋙ boundedConstructibleLowerStar ℓ g :=
  sorry

end LowerStar

section OpenImmersion

variable {U X : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

/-- **(Shriek)** on bounded constructible complexes for `𝒪_E ⟶ ℚ̄_ℓ` and an open immersion `j`:
`j_!^{𝒪_E} ⋙ T_X ≅ T_U ⋙ j_!^{ℚ̄_ℓ}`, the comparisons for `𝒪_E ⟶ E`
(`boundedConstructibleOpenImmersionLowerShriekExtendScalarsIso`) and for `E ⟶ ℚ̄_ℓ`
(`boundedConstructibleOpenImmersionLowerShriekToPadicAlgClIso`). -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekIntegersToPadicAlgClIso
    (j : U ⟶ X) [IsOpenImmersion j.left] :
    boundedConstructibleOpenImmersionLowerShriek (Profinite.padicIntegersRingObj ℓ E.1) ℓ j ⋙
        boundedConstructibleIntegersToPadicAlgCl ℓ E X ≅
      boundedConstructibleIntegersToPadicAlgCl ℓ E U ⋙
        boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j :=
  sorry

end OpenImmersion

end CondensedRing

end AlgebraicGeometry.ProEtale
