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
`det-prop-scalar-six-direct-image` for `𝒪_E ⟶ ℚ̄_ℓ`) and with the extension by zero along an
open immersion
(`ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekIntegersToPadicAlgClIso`),
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
        ((boundedConstructibleExtendScalars X' ℓ E).obj K₀') ≅ K') := by
  obtain ⟨E₁, K₁, ⟨e₁⟩⟩ := constructibleCocone_essSurjObj X ℓ K
  obtain ⟨E₂, K₂, ⟨e₂⟩⟩ := constructibleCocone_essSurjObj X' ℓ K'
  obtain ⟨F, h₁, h₂⟩ := exists_ge_ge E₁ E₂
  obtain ⟨K₀, ⟨e₀⟩⟩ := exists_boundedConstructibleExtendScalars_obj_iso X ℓ F
    ((constructibleExtendScalars X ℓ h₁).obj K₁)
  obtain ⟨K₀', ⟨e₀'⟩⟩ := exists_boundedConstructibleExtendScalars_obj_iso X' ℓ F
    ((constructibleExtendScalars X' ℓ h₂).obj K₂)
  exact ⟨F, K₀, K₀',
    ⟨(constructibleToPadicAlgCl X ℓ F).mapIso e₀ ≪≫
      (constructibleToPadicAlgClCompIso X ℓ h₁).app K₁ ≪≫ e₁⟩,
    ⟨(constructibleToPadicAlgCl X' ℓ F).mapIso e₀' ≪≫
      (constructibleToPadicAlgClCompIso X' ℓ h₂).app K₂ ≪≫ e₂⟩⟩

namespace CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

section LowerStar

variable {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType Z.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] in
/-- The derived comparison **(Push)** `ℚ̄_ℓ ⊗ᴸ_E Rg_* K ⟶ Rg_* (ℚ̄_ℓ ⊗ᴸ_E K)` is an isomorphism on
bounded constructible complexes, these being bounded below
(`isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE`). -/
lemma isIso_whiskerLeft_ι_derivedPushHom_padicSubfieldRingObjToPadicAlgCl (g : Z ⟶ Y) :
    IsIso (Functor.whiskerLeft (boundedConstructible (padicSubfieldRingObj Z.left ℓ E)).ι
      (derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) g.left)) := by
  have : QuasiCompact g.left := by
    have : QuasiCompact (g.left ≫ Y.hom) := by rw [Over.w g]; infer_instance
    exact QuasiCompact.of_comp g.left Y.hom
  have : QuasiSeparated g.left := by
    have : QuasiSeparated (g.left ≫ Y.hom) := by rw [Over.w g]; infer_instance
    exact QuasiSeparated.of_comp g.left Y.hom
  refine (NatTrans.isIso_iff_isIso_app _).2 fun K ↦ ?_
  have : K.obj.IsGE K.property.1.1.choose := K.property.1.1.choose_spec
  exact isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE ℓ E g.left K.obj
    K.property.1.1.choose

/-- **(Push)** on bounded constructible complexes, for the inclusion `E ⟶ ℚ̄_ℓ` and any morphism
`g` of separated `k`-schemes of finite type: `Rg_*^E ⋙ T_Y ≅ T_Z ⋙ Rg_*^{ℚ̄_ℓ}`, the restriction of
`ProEtale.CondensedRing.derivedPushHom`, which is an isomorphism on bounded constructible complexes
(`isIso_whiskerLeft_ι_derivedPushHom_padicSubfieldRingObjToPadicAlgCl`). Unlike
`boundedConstructibleLowerStarToPadicAlgClIso`, `g` need not be proper. -/
noncomputable def boundedConstructibleLowerStarToPadicAlgClIsoOfQcqs (g : Z ⟶ Y) :
    ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E g ⋙
        boundedConstructibleToPadicAlgCl Y.left ℓ E ≅
      boundedConstructibleToPadicAlgCl Z.left ℓ E ⋙
        boundedConstructibleLowerStar ℓ g :=
  have := isIso_whiskerLeft_ι_derivedPushHom_padicSubfieldRingObjToPadicAlgCl ℓ E g
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (boundedConstructibleToPadicAlgClCompatibility Y.left ℓ E) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (ContinuousMapRingObj.boundedConstructibleLowerStarCompatibility ℓ E g) _ ≪≫
      Functor.associator _ _ _ ≪≫
      asIso (Functor.whiskerLeft (boundedConstructible (padicSubfieldRingObj Z.left ℓ E)).ι
        (derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) g.left)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedConstructibleToPadicAlgClCompatibility Z.left ℓ E).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarCompatibility ℓ g).symm ≪≫
      (Functor.associator _ _ _).symm)

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
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (boundedConstructibleLowerStarExtendScalarsIso ℓ E g)
      (constructibleToPadicAlgCl Y.left ℓ E) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (boundedConstructibleExtendScalars Z.left ℓ E)
      (boundedConstructibleLowerStarToPadicAlgClIsoOfQcqs ℓ E g) ≪≫
    (Functor.associator _ _ _).symm

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
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (boundedConstructibleOpenImmersionLowerShriekExtendScalarsIso ℓ E j)
      (constructibleToPadicAlgCl X.left ℓ E) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (boundedConstructibleExtendScalars U.left ℓ E)
      (boundedConstructibleOpenImmersionLowerShriekToPadicAlgClIso ℓ E j) ≪≫
    (Functor.associator _ _ _).symm

end OpenImmersion

end CondensedRing

end AlgebraicGeometry.ProEtale
