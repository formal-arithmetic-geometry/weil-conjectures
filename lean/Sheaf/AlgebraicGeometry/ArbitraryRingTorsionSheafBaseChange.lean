/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import Sheaf.AlgebraicGeometry.TorsionEtaleSheaf
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Coefficients
import Sheaf.AlgebraicGeometry.ModuleAbelianDerivedExchangeCompatibility
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations

/-!
# Sheaf-level proper base change for arbitrary coefficient rings

Source: Stacks Project, Etale Cohomology, Lemma 0A4B, proof paragraphs 2–3
(blueprint: lem-weil-pbc-arbitrary-ring-torsion-sheaf-base-change).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Source: Stacks Project, Lemma 0A4B, proof paragraphs 2–3, with coefficients in `Λ`
(blueprint: lem-weil-pbc-arbitrary-ring-torsion-sheaf-base-change).
Coefficient-wise injective acyclicity for `Λ/ℓ` implies derived base change for each
`Λ`-module sheaf whose underlying abelian sheaf is torsion.

Proof:
1. The canonical inverse-image and derived direct-image coefficient comparisons identify
   the underlying abelian higher direct image of a pulled-back module sheaf with the
   corresponding abelian expression in `hIA`. Exact forgetting commutes with homology
   and is faithful, so vanishing of this expression implies module-valued injective
   acyclicity over every `Λ/ℓ`.
2. Apply the library's `hasTorsionBaseChange_of_hasInjectiveAcyclicity`. Its proof performs
   the prime-quotient injective-resolution argument, prime-factor induction, and
   filtered-colimit passage of Stacks 0A4B. This retains the unit's proof route.
3. The torsion-sheaf characterization turns `hF` into local torsion of the underlying
   abelian sheaf, equivalently `IsTorsionModuleSheaf F`. Its degree-zero complex therefore
   has torsion homology, and the module-valued exchange is invertible there.
4. Canonical coefficient comparisons intertwine module and abelian derived exchange.
   Their endpoint maps are invertible, so the specified abelian exchange is invertible
   on the forgotten complex. Naturality transports this to the degree-zero complex
   of the underlying abelian sheaf. -/
theorem isIso_derivedBaseChangeMapPlus_of_primeQuotient_injective_acyclicity
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (hIA : ∀ (ℓ : ℕ), ℓ.Prime →
      ∀ {Y' X' : Scheme.{u}} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X},
        IsPullback g' f' f g →
        ∀ (I : Sheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} (Λ ⧸ Ideal.span ({(ℓ : Λ)} : Set Λ)))),
          Injective I → ∀ q : ℤ, 0 < q →
            IsZero ((DerivedCategory.Plus.homologyFunctor
              (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
              ((lowerStar AddCommGrpCat.{u + 1} f').rightDerivedFunctorPlus.obj
                ((DerivedCategory.Plus.singleFunctor
                  (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
                  ((upperStar AddCommGrpCat.{u + 1} g').obj
                    ((sheafCompose X.smallEtaleTopology
                      (forget₂ (ModuleCat.{u + 1}
                        (Λ ⧸ Ideal.span ({(ℓ : Λ)} : Set Λ)))
                        AddCommGrpCat.{u + 1})).obj I))))))
    {Y' X' : Scheme.{u}} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f g)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : Scheme.IsTorsionAbelianSheaf
      ((sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)) :
    IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
      ((DerivedCategory.Plus.singleFunctor
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
        ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F))) := by
  -- Convert the abelian vanishing hypothesis to the module-coefficient interface.
  have hIAm : ∀ ℓ : ℕ, ℓ.Prime →
      HasInjectiveAcyclicity (Λ ⧸ Ideal.span ({(ℓ : Λ)} : Set Λ)) f := by
    intro ℓ hℓ Y₁ X₁ g₁ f₁ g₁' sq₁ I _ hI q hq
    let R := Λ ⧸ Ideal.span ({(ℓ : Λ)} : Set Λ)
    let M := (upperStar (ModuleCat.{u + 1} R) g₁').obj I
    let L := (DerivedCategory.Plus.singleFunctor
      (Sheaf X₁.smallEtaleTopology (ModuleCat.{u + 1} R)) 0).obj M
    let e : (moduleAbelianForget R Y₁).mapDerivedCategoryPlus.obj
          ((lowerStar (ModuleCat.{u + 1} R) f₁).rightDerivedFunctorPlus.obj L) ≅
        (lowerStar AddCommGrpCat.{u + 1} f₁).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf X₁.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
              ((upperStar AddCommGrpCat.{u + 1} g₁').obj
                ((moduleAbelianForget R X).obj I))) :=
      (moduleAbelianDerivedLowerStarIso R f₁).app L ≪≫
        (lowerStar AddCommGrpCat.{u + 1} f₁).rightDerivedFunctorPlus.mapIso
          (((moduleAbelianForget R X₁).mapDerivedCategoryPlusSingleFunctor 0).app M ≪≫
            (DerivedCategory.Plus.singleFunctor
              (Sheaf X₁.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).mapIso
                ((moduleAbelianUpperStarIso R g₁').symm.app I))
    have hz := IsZero.of_iso (hIA ℓ hℓ sq₁ I hI q hq)
      (((moduleAbelianForget R Y₁).mapDerivedCategoryPlusHomologyFunctorIso q).app
          ((lowerStar (ModuleCat.{u + 1} R) f₁).rightDerivedFunctorPlus.obj L) ≪≫
        (DerivedCategory.Plus.homologyFunctor
          (Sheaf Y₁.smallEtaleTopology AddCommGrpCat.{u + 1}) q).mapIso e)
    change IsZero ((DerivedCategory.Plus.homologyFunctor
      (Sheaf Y₁.smallEtaleTopology (ModuleCat.{u + 1} R)) q).obj
        ((lowerStar (ModuleCat.{u + 1} R) f₁).rightDerivedFunctorPlus.obj L))
    apply (IsZero.iff_id_eq_zero _).2
    apply (moduleAbelianForget R Y₁).map_injective
    rw [CategoryTheory.Functor.map_id, Functor.map_zero]
    exact hz.eq_of_src _ _
  -- Reuse the existing prime-factor and filtered-colimit argument.
  have hbc := hasTorsionBaseChange_of_hasInjectiveAcyclicity Λ f hIAm
  have htor : Scheme.IsTorsionModuleSheaf F :=
    (Scheme.isTorsionModuleSheaf_iff_isTorsion F).2
      ((Scheme.isTorsionAbelianSheaf_characterizations _).1.mp hF)
  let K := (DerivedCategory.Plus.singleFunctor
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj F
  have hK : DerivedCategory.Plus.moduleTorsionHomology Λ X K :=
    DerivedCategory.Plus.moduleTorsionHomology_singleFunctor_obj Λ X F
  have : IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) :=
    hbc sq K hK
  -- Transport the specified exchange map, using the canonical compatibility equation.
  have hcompat := moduleAbelianDerivedExchange_compatibility Λ sq.toCommSq K
  have hforgot : IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
      sq.toCommSq).app ((moduleAbelianForget Λ X).mapDerivedCategoryPlus.obj K)) := by
    rw [← isIso_comp_left_iff (moduleAbelianDerivedExchangeSourceIso Λ f g K).hom,
      ← hcompat]
    infer_instance
  exact (NatTrans.isIso_app_iff_of_iso _
    (((moduleAbelianForget Λ X).mapDerivedCategoryPlusSingleFunctor 0).app F)).mp hforgot

end AlgebraicGeometry.Etale
