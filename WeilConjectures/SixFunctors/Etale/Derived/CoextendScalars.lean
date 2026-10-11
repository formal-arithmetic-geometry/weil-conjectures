/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.Sites.InjectiveSheafSmulEpi
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Derived coextension of scalars commutes with the derived direct image

For a ring morphism `φ : Λ →+* Λ'`, coextension of scalars `M ↦ Hom_Λ(Λ', M)` sends étale sheaves
of `Λ`-modules to étale sheaves of `Λ'`-modules. It is right adjoint to the exact restriction of
scalars, so it preserves K-injective complexes, and it commutes with the direct image `g_*`
(both are computed objectwise). Hence its total right derived functor commutes with `Rg_*`:

`Rg_* ⋙ R coext ≅ R coext ⋙ Rg_*`.

For `Λ = 𝒪_E` and `Λ' = 𝒪_E/ϖ` the functor `R coext = RHom_{𝒪_E}(𝒪_E/ϖ, -)` is the reduction
modulo `ϖ` shifted by `-1`, read in `D(-, 𝒪_E/ϖ)`; this is a first step towards comparing
the integral and the finite stages of the projection formula (`sk-thm-sf-pf-adic`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')

instance :
    PreservesLimitsOfSize.{u, u + 1} (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ) :=
  (ModuleCat.restrictCoextendScalarsAdj.{u + 1} φ).rightAdjoint_preservesLimits

instance : (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ).IsRightAdjoint :=
  (ModuleCat.restrictCoextendScalarsAdj.{u + 1} φ).isRightAdjoint

/-- Coextension of scalars along `φ : Λ →+* Λ'`, from étale sheaves of `Λ`-modules to étale
sheaves of `Λ'`-modules. -/
noncomputable abbrev coextendScalars (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ') :=
  sheafCompose X.smallEtaleTopology (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ)

instance (X : Scheme.{u}) : (coextendScalars φ X).Additive where
  map_add {_ _ _ _} := by
    ext : 3
    rfl

instance (X : Scheme.{u}) :
    (Sheaf.restrictScalars X.smallEtaleTopology φ).PreservesHomology :=
  Functor.preservesHomology_of_preservesMonos_and_cokernels _

/-- Coextension of scalars preserves K-injective complexes, being right adjoint to the exact
restriction of scalars. -/
instance (X : Scheme.{u}) : (coextendScalars φ X).PreservesKInjectiveComplexes :=
  (Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).preservesKInjectiveComplexes

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- Coextension of scalars commutes with the direct image, both being computed objectwise. -/
noncomputable def lowerStarCompCoextendScalarsIso :
    (g)_*[ModuleCat.{u + 1} Λ] ⋙ coextendScalars φ Y ≅
      coextendScalars φ Z ⋙ (g)_*[ModuleCat.{u + 1} Λ'] :=
  Iso.refl _

/-- **Derived coextension of scalars commutes with `Rg_*`.** -/
noncomputable def rightDerivedLowerStarCompCoextendScalarsIso :
    ((g)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctor ⋙
        (coextendScalars φ Y).rightDerivedFunctor ≅
      (coextendScalars φ Z).rightDerivedFunctor ⋙
        ((g)_*[ModuleCat.{u + 1} Λ']).rightDerivedFunctor :=
  Functor.rightDerivedFunctorCompIso' _ _ (lowerStarCompCoextendScalarsIso φ g) ≪≫
    (Functor.rightDerivedFunctorCompIso' _ _ (Iso.refl _)).symm

section Detect

variable {X : Scheme.{u}} (ϖ : Λ)

/-- The short complex `Hom_Λ(Λ/ϖ, F) ⟶ F ⟶ F` of étale sheaves, the first map being the counit of
restriction and coextension of scalars along `Λ → Λ/ϖ` and the second multiplication by `ϖ`. -/
noncomputable def coextendQuotientSheafShortComplex
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  ShortComplex.mk
    ((Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology
      (Ideal.Quotient.mk (Ideal.span {ϖ}))).counit.app F)
    (ϖ • 𝟙 F) (by
      ext U : 3
      exact (ModuleCat.coextendQuotientShortComplex ϖ (F.obj.obj U)).zero)

lemma coextendQuotientSheafShortComplex_map_eval
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (U : X.Etaleᵒᵖ) :
    ((coextendQuotientSheafShortComplex ϖ F).map
      (sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj U)) =
      ModuleCat.coextendQuotientShortComplex ϖ (F.obj.obj U) :=
  rfl

variable {ϖ} in
/-- For an injective étale sheaf `F` and a nonzerodivisor `ϖ`, the sequence
`0 ⟶ Hom_Λ(Λ/ϖ, F) ⟶ F ⟶ F ⟶ 0` (multiplication by `ϖ`) is short exact. -/
lemma shortExact_coextendQuotientSheafShortComplex (hϖ : ϖ ∈ nonZeroDivisors Λ)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective F] :
    (coextendQuotientSheafShortComplex ϖ F).ShortExact := by
  let S := coextendQuotientSheafShortComplex ϖ F
  have hpre : (S.map (sheafToPresheaf _ _)).Exact := by
    rw [ShortComplex.exact_iff_isZero_homology]
    refine Functor.isZero _ fun U ↦ ?_
    have h := ModuleCat.exact_coextendQuotientShortComplex ϖ (F.obj.obj U)
    rw [ShortComplex.exact_iff_isZero_homology] at h
    exact h.of_iso ((S.map (sheafToPresheaf _ _)).mapHomologyIso
      ((CategoryTheory.evaluation _ _).obj U)).symm
  have hmono : Mono (S.map (sheafToPresheaf _ _)).f := by
    have (U : X.Etaleᵒᵖ) : Mono ((S.map (sheafToPresheaf _ _)).f.app U) :=
      ModuleCat.mono_coextendQuotientShortComplex_f ϖ (F.obj.obj U)
    exact NatTrans.mono_of_mono_app _
  have : Mono S.f := (sheafToPresheaf _ _).mono_of_mono_map hmono
  have : Epi S.g := Sheaf.epi_smul_id_of_injective.{u + 1} F hϖ
  refine ⟨?_⟩
  have e : S.map (sheafToPresheaf _ _ ⋙ presheafToSheaf _ _) ≅ S :=
    S.mapNatIso (asIso (sheafificationAdjunction _ _).counit)
  exact (ShortComplex.exact_iff_of_iso e).1 (hpre.map (presheafToSheaf _ _))

end Detect

end Etale

end AlgebraicGeometry
