/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.SmoothResidue
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import WeilConjectures.TraceFormula.Specialization.DeformationModel

/-!

# Integral smooth base change along affine spaces for the geometric generic fibre

For the inclusion `j : 𝒴_Ω ⟶ 𝒴` of the geometric generic fibre of the deformation model
`𝒴 = 𝒟_I Y` and the projection `π : 𝔸ⁿ_𝒴 ⟶ 𝒴`, the base change map `Lπ^* Rj_* ⟶ Rj'_* Lπ'^*` with
coefficients `𝒪_E` is invertible at `Lε^* K₀` for every bounded constructible `𝒪_E`-complex `K₀` on
`Y` (`ProEtale.CondensedRing.isIso_baseChangeMap_affineSpace_deformationModel_app_padicIntegers`).

## Proof

Let `C` be the cone of the base change map at `Lε^* K₀` and `ϖ` a uniformizer of `𝒪_E`. The
reduction `- ⊗ᴸ_{𝒪_E} 𝔽_E` of the base change map is the base change map with coefficients `𝔽_E`
at `Lε^* K₀ ⊗ᴸ 𝔽_E ≅ Lε^* (K₀ ⊗ᴸ 𝔽_E)`, invertible by smooth base change with finite coefficients.
So `C ⊗ᴸ 𝔽_E = 0`, and `ϖ` acts invertibly on `C`
(`ProEtale.CondensedRing.isIso_derivedRegularEndSMul_cone_baseChangeMap_app_of_smooth`). If the
source `Lπ^* Rj_* Lε^* K₀` and the target `Rj'_* Lπ'^* Lε^* K₀` are derived `ϖ`-complete
(`CategoryTheory.Mod.IsDerivedRegularEndComplete`), then `C = 0`
(`CategoryTheory.Mod.isZero_obj₃_of_isDerivedRegularEndComplete`).

## Sorried input

The derived `ϖ`-completeness of the source and the target,
`ProEtale.CondensedRing.isDerivedRegularEndComplete_baseChangeMap_affineSpace_deformationModel`,
is `sorry`ed. For the target, it would follow from the derived completeness of bounded
constructible complexes (here `Lπ'^* Lε^* K₀`), since `Rj'_*` is right adjoint to `Lj'^*`, which
preserves complexes on which `ϖ` acts invertibly; but derived completeness of bounded constructible
`𝒪_{E,X}`-complexes (that `𝒪_{E,X} = R lim 𝒪_{E,X} ⧸ ϖⁿ` in the replete pro-étale topos and the
dévissage of constructible complexes) is not available. For the source, completeness of `Lπ^* N`
for a derived complete `N = Rj_* Lε^* K₀` is not formal either: `N` is not constructible (`j` is
not of finite type) and the pullback along `π` does not commute with derived limits in general.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (k' : Type u) [Field k'] [Algebra k k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

/-- **Derived completeness of the source and target of integral smooth base change** (`sorry`ed,
see the module docstring): for the inclusion `j : 𝒴_Ω ⟶ 𝒴` of the geometric generic fibre of the
deformation model `𝒴 = 𝒟_I Y`, the projection `π : 𝔸ⁿ_𝒴 ⟶ 𝒴`, the base change
`j' : 𝒴_Ω ×_𝒴 𝔸ⁿ_𝒴 ⟶ 𝔸ⁿ_𝒴`, `π' : 𝒴_Ω ×_𝒴 𝔸ⁿ_𝒴 ⟶ 𝒴_Ω`, a bounded constructible `𝒪_E`-complex
`K₀` on `Y` and a uniformizer `ϖ` of `𝒪_E`, the complexes `Lπ^* Rj_* Lε^* K₀` and
`Rj'_* Lπ'^* Lε^* K₀` of `𝒪_{E,𝔸ⁿ_𝒴}`-module objects are derived `ϖ`-complete: every morphism to
one of their shifts from a complex on which `ϖ` acts invertibly vanishes. -/
theorem isDerivedRegularEndComplete_baseChangeMap_affineSpace_deformationModel
    {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (I : Y.left.IdealSheafData) (n : ℕ) (E : FiniteIntermediateField ℓ)
    {K₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y.left))}
    (hK₀ : boundedConstructible _ K₀) (ϖ : PadicAlgCl.integers ℓ E.1)
    (hϖ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1) = Ideal.span {ϖ}) :
    Mod.IsDerivedRegularEndComplete
        (padicIntegersRegularEnd 𝔸(ULift.{u} (Fin n); (deformationModel Y I k').total) ℓ E ϖ)
        ((R(((deformationModel Y I k').j)_*⟦Profinite.padicIntegersRingObj ℓ E.1⟧) ⋙
          L((𝔸(ULift.{u} (Fin n); (deformationModel Y I k').total) ↘
            (deformationModel Y I k').total)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj
          ((L(((deformationModel Y I k').ε)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj K₀)) ∧
      Mod.IsDerivedRegularEndComplete
        (padicIntegersRegularEnd 𝔸(ULift.{u} (Fin n); (deformationModel Y I k').total) ℓ E ϖ)
        ((L((pullback.fst (deformationModel Y I k').j
            (𝔸(ULift.{u} (Fin n); (deformationModel Y I k').total) ↘
              (deformationModel Y I k').total))^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧) ⋙
          R((pullback.snd (deformationModel Y I k').j
            (𝔸(ULift.{u} (Fin n); (deformationModel Y I k').total) ↘
              (deformationModel Y I k').total))_*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj
          ((L(((deformationModel Y I k').ε)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj K₀)) :=
  sorry

/-- **Integral smooth base change along affine spaces for the geometric generic fibre** (blueprint
`sbc-thm-bounded-derived-smooth-base-change`, for `𝒪_E`-coefficients and the projection
`π : 𝔸ⁿ_𝒴 ⟶ 𝒴`): for the inclusion `j : 𝒴_Ω ⟶ 𝒴` of the geometric generic fibre of the deformation
model `𝒴 = 𝒟_I Y` and the cartesian square of `j` along `π`, the base change morphism
`Lπ^* Rj_* ⟶ Rj'_* Lπ'^*` with coefficients `𝒪_E` is invertible at `Lε^* K₀` for every bounded
constructible `𝒪_E`-complex `K₀` on `Y`. The uniformizer `ϖ` acts invertibly on its cone, by smooth
base change with finite coefficients, and the cone of a morphism between derived `ϖ`-complete
complexes on which `ϖ` acts invertibly vanishes; the derived completeness is `sorry`ed
(`isDerivedRegularEndComplete_baseChangeMap_affineSpace_deformationModel`). -/
theorem isIso_baseChangeMap_affineSpace_deformationModel_app_padicIntegers
    {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (I : Y.left.IdealSheafData) (n : ℕ) (E : FiniteIntermediateField ℓ)
    {K₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y.left))}
    (hK₀ : boundedConstructible _ K₀) :
    IsIso ((baseChangeMap (Profinite.padicIntegersRingObj ℓ E.1)
      (IsPullback.of_hasPullback (deformationModel Y I k').j
        (𝔸(ULift.{u} (Fin n); (deformationModel Y I k').total) ↘
          (deformationModel Y I k').total)).toCommSq).app
      ((L(((deformationModel Y I k').ε)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj K₀)) := by
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : IsNoetherian Y.left := {}
  have : QuasiCompact (deformationModel Y I k').j := by
    rw [deformationModel_j, deformationGenericToTotal]
    infer_instance
  have : QuasiSeparated (deformationModel Y I k').j := by
    rw [deformationModel_j, deformationGenericToTotal]
    infer_instance
  have : Smooth (𝔸(ULift.{u} (Fin n); (deformationModel Y I k').total) ↘
      (deformationModel Y I k').total) :=
    SmoothOfRelativeDimension.smooth (Nat.card (ULift.{u} (Fin n))) _
  have hℓk : IsUnit (ℓ : k) := by
    refine IsUnit.mk0 _ fun h ↦ (Fact.out : ringChar k ≠ ℓ) ?_
    exact (Nat.prime_dvd_prime_iff_eq (Fact.out : (ringChar k).Prime) Fact.out).1
      ((ringChar.spec k ℓ).1 h)
  have hℓ : IsUnit (ℓ : Γ((deformationModel Y I k').total, ⊤)) := by
    simpa using (hℓk.map (ΓSpecIso (.of k)).inv.hom).map
      (deformationTotalToBase Y I k' ≫ Y.hom).appTop.hom
  have hϖ := PadicAlgCl.isPrincipal_maximalIdeal_integers ℓ E.1
  obtain ⟨ϖ, hϖ⟩ := hϖ
  rw [Ideal.submodule_span_eq] at hϖ
  have hb := hK₀.1.1
  obtain ⟨m, hm⟩ := hb
  have : ((L(((deformationModel Y I k').ε)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj
      K₀).IsGE m := isGE_leftDerivedUpperStar_obj _ _ K₀ m
  have hT := distinguished_cocone_triangle ((baseChangeMap
    (Profinite.padicIntegersRingObj ℓ E.1) (IsPullback.of_hasPullback (deformationModel Y I k').j
      (𝔸(ULift.{u} (Fin n); (deformationModel Y I k').total) ↘
        (deformationModel Y I k').total)).toCommSq).app
    ((L(((deformationModel Y I k').ε)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj K₀))
  obtain ⟨C, v, δ, hT⟩ := hT
  have hC := isIso_derivedRegularEndSMul_cone_baseChangeMap_app_of_smooth ℓ E
    (IsPullback.of_hasPullback _ _) hℓ _ m
    (boundedConstructible_derivedExtendScalars_residueField_leftDerivedUpperStar_obj ℓ E _ K₀
      hK₀) hT ϖ hϖ
  have hc :=
    isDerivedRegularEndComplete_baseChangeMap_affineSpace_deformationModel k' I n E hK₀ ϖ hϖ
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).1
    (Mod.isZero_obj₃_of_isDerivedRegularEndComplete hT hc.1 hc.2 hC)

end AlgebraicGeometry.ProEtale.CondensedRing
