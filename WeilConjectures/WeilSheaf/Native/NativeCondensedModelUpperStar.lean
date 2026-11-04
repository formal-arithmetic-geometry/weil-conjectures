/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelEquivalenceFunctoriality
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseInternalHom
public import WeilConjectures.SixFunctors.ProEtale.Comparison.ForgetUpperStarMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.CategoryTheory.ModuleObjects.RelativeTensorCoequalizer
public import WeilConjectures.WeilSheaf.Native.NativeCondensedModelTensor

/-!
# The condensed model of `ℓ`-adic sheaves commutes monoidally with pullback

Let `f : Z ⟶ Y` be a morphism of schemes and `E_X : AdicSheaf ℓ X ≌ Mod_{Λ_X}` the condensed model
of `ℓ`-adic sheaves (`AlgebraicGeometry.ProEtale.adicSheafEquivCondensedMod`), `E_X` being
`forgetAb ⋙ comap κ_X` on the underlying abelian sheaves. We construct an isomorphism
`E_Y ⋙ f^* ≅ f^*ᵃ ⋙ E_Z` (`AlgebraicGeometry.ProEtale.condensedModUpperStarIso`) whose
underlying map of abelian sheaves is the identification
`f^*(U M) ≅ U(f^* M)` of `AlgebraicGeometry.ProEtale.sheafComposeForget₂CompUpperStarIso`, the
condensed pullback `f^*` of module objects being identified with `mapMod(f^*) ⋙ comap α_f⁻¹`
(`CategoryTheory.Mod.extendScalarsIsoComapInv`).

This isomorphism is monoidal: it carries the pullback–tensor comparison
`AlgebraicGeometry.ProEtale.adicUpperStarTensorLeftIso` of `ℓ`-adic sheaves to the comonoidal
structure of the condensed pullback
(`AlgebraicGeometry.ProEtale.condensedModUpperStarIso_tensor`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] {Z Y : Scheme.{u}} (f : Z ⟶ Y)

/-- The ring objects: the identification `κ_Z : Λ_Z ≅ U ℚ̄_ℓ,Z` followed by `U` of the ring
isomorphism `ℚ̄_ℓ,Z ⟶ f^* ℚ̄_ℓ,Y` agrees with `α_f⁻¹ : Λ_Z ⟶ f^* Λ_Y` followed by `f^* κ_Y` and
the identification `f^* (U ℚ̄_ℓ,Y) ≅ U (f^* ℚ̄_ℓ,Y)`. -/
lemma condensedRingObjIsoForgetAb_hom_comp_map_adicUpperStarRingHom :
    (condensedRingObjIsoForgetAb l Z).hom ≫
        (weilCoefficientsForgetAb l Z).map (adicUpperStarRingHom l f) =
      inv (condensedPullbackHom (Profinite.padicAlgClRingObj l) f) ≫
        (f)^*[Ab.{u + 1}].map (condensedRingObjIsoForgetAb l Y).hom ≫
        (sheafComposeForget₂CompUpperStarIso (ULift.{u + 1} (PadicAlgCl l)) f).hom.app
          (adicConstantSheaf l Y) :=
  sorry

/-- **The condensed model commutes with pullback**: `E_Y ⋙ f^* ≅ f^*ᵃ ⋙ E_Z`. The condensed
pullback is `mapMod(f^*) ⋙ comap α_f⁻¹` (`CategoryTheory.Mod.extendScalarsIsoComapInv`), and on
underlying abelian sheaves the isomorphism is `f^*(U M) ≅ U(f^* M)`
(`AlgebraicGeometry.ProEtale.sheafComposeForget₂CompUpperStarIso`). -/
noncomputable def condensedModUpperStarIso :
    (adicSheafEquivCondensedMod l Y).functor ⋙
        CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f ≅
      adicUpperStar l f ⋙ (adicSheafEquivCondensedMod l Z).functor :=
  sorry

/-- **The condensed model commutes monoidally with pullback.** For `ℓ`-adic sheaves `M`, `N` on
`Y`, the isomorphism `condensedModUpperStarIso` carries the pullback–tensor comparison
`f^*ᵃ(M ⊗ N) ≅ f^*ᵃ M ⊗ f^*ᵃ N` of `ℓ`-adic sheaves (`adicUpperStarTensorLeftIso`, with the
coequalizer tensor identified with the monoidal one by `Mod.relativeTensorRightIso`) to the
comonoidal structure `δ` of the condensed pullback, up to the monoidal comparisons
`adicSheafEquivCondensedModTensorIso` of the condensed models. -/
lemma condensedModUpperStarIso_tensor (M N : AdicSheaf l Y) :
    (condensedModUpperStarIso l f).hom.app ((Mod.tensorLeft N).obj M) ≫
        (adicSheafEquivCondensedMod l Z).functor.map
          ((adicUpperStarTensorLeftIso l f N).hom.app M ≫
            (Mod.relativeTensorRightIso ((adicUpperStar l f).obj N)).hom.app
              ((adicUpperStar l f).obj M)) ≫
        (adicSheafEquivCondensedModTensorIso l Z ((adicUpperStar l f).obj M)
          ((adicUpperStar l f).obj N)).inv =
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).map
          ((adicSheafEquivCondensedMod l Y).functor.map
              ((Mod.relativeTensorRightIso N).hom.app M) ≫
            (adicSheafEquivCondensedModTensorIso l Y M N).inv) ≫
        Functor.OplaxMonoidal.δ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f)
          ((adicSheafEquivCondensedMod l Y).functor.obj M)
          ((adicSheafEquivCondensedMod l Y).functor.obj N) ≫
        ((condensedModUpperStarIso l f).hom.app M ⊗ₘ (condensedModUpperStarIso l f).hom.app N) :=
  sorry

end AlgebraicGeometry.ProEtale
