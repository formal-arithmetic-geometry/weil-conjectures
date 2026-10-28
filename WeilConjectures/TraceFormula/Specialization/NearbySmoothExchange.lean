/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicIntegralModel
public import WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.SmoothPadicIntegers
public import WeilConjectures.TraceFormula.Specialization.DefectCentreMap
public import WeilConjectures.TraceFormula.Specialization.NearbySmoothExchangeLocal
public import WeilConjectures.TraceFormula.Specialization.NormalizePrecoherent

/-!

# The smooth exchange of nearby cycles for the deformation to the normal cone

For a smooth morphism `f : X ⟶ Y` of separated `k`-schemes of finite type and `J = f⁻¹ I`, the
morphism of deformation models `f̃ : 𝒟_J X ⟶ 𝒟_I Y` is the base change of `f`, hence smooth
(`ProEtale.CondensedRing.smooth_deformationTotalMap`), and its square of geometric generic fibres is
cartesian. By smooth base change, its pullback exchange `α_{f̃} : Lf_s^* Ψ_Y ⟶ Ψ_X Lf^*` is an
isomorphism on bounded constructible `ℚ̄_ℓ`-complexes
(`ProEtale.CondensedRing.isIso_pullbackExchange_deformationModel_app_of_smooth`).

## Proof

`ProEtale.CondensedRing.isIso_pullbackExchange_deformationModel_app_of_smooth` (the smooth half
of blueprint `det-sp-nearby-cycles-exchanges` (1), applied to the smooth morphism of deformation
models of blueprint `det-sp-dnc-base-change` (3)) is reduced, by
`ProEtale.CondensedRing.NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_isIso_baseChangeMap_app`
and `ProEtale.CondensedRing.isIso_baseChangeMap_app_of_smooth` (locally on the source a smooth
morphism is étale over an affine space), to smooth base change along the projections
`𝔸ⁿ_𝒴 ⟶ 𝒴` for the inclusion `j` of the geometric generic fibre,
`ProEtale.CondensedRing.isIso_baseChangeMap_affineSpace_deformationModel_app`. The morphism `j`
is not of finite type, so neither side of that base change is constructible. It is deduced from
an integral model `K₀` of `K`: the integral base change map is invertible by derived Nakayama
for derived complete complexes
(`ProEtale.CondensedRing.isIso_baseChangeMap_app_padicIntegers_of_smooth`), and the passage
`𝒪_E → ℚ̄_ℓ` is `ProEtale.CondensedRing.isIso_baseChangeMap_app_padicAlgCl_of_padicIntegers`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (k' : Type u) [Field k'] [Algebra k k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

/-- The geometric generic fibre of a deformation model is noetherian: it is of finite type over
the field `Ω`. -/
lemma isNoetherian_deformationGeneric {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom] (I : Y.left.IdealSheafData) :
    IsNoetherian (deformationModel Y I k').generic := by
  change IsNoetherian (deformationGeneric Y I k')
  have : IsLocallyNoetherian (deformationGeneric Y I k') :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.snd (deformationTotalToTrait Y I k') (traitGenericPoint k'))
  have : CompactSpace (deformationGeneric Y I k') :=
    QuasiCompact.compactSpace_of_compactSpace
      (pullback.snd (deformationTotalToTrait Y I k') (traitGenericPoint k'))
  exact ⟨⟩

/-- **Smooth base change along affine spaces for the geometric generic fibre** (the case of the
projection `π : 𝔸ⁿ_𝒴 ⟶ 𝒴` of the smooth base change used in blueprint
`det-sp-nearby-cycles-exchanges` (1)): for the inclusion `j : 𝒴_Ω ⟶ 𝒴` of the geometric generic
fibre of the deformation model `𝒴 = 𝒟_I Y` and the cartesian square of `j` along `π`, the base
change morphism `Lπ^* Rj_* ⟶ Rj'_* Lπ'^*` is invertible at `Lε^* K` for every bounded
constructible `ℚ̄_ℓ`-complex `K` on `Y`.

The morphism `j` is not of finite type. As in the proof of blueprint `sk-thm-sbc-coefficients`,
`K` has an integral model `K₀` over some `𝒪_E` (`ProEtale.exists_padicAlgCl_iso_integralModel`),
the pullback `Lε^*` commutes with the extensions of scalars `𝒪_E ⟶ E ⟶ ℚ̄_ℓ`
(`ProEtale.CondensedRing.derivedPullIso`), the base change morphism at `ℚ̄_ℓ ⊗ᴸ (E ⊗ᴸ Lε^* K₀)`
is invertible as soon as the integral one at `Lε^* K₀` is
(`ProEtale.CondensedRing.isIso_baseChangeMap_app_padicAlgCl_of_padicIntegers`), and the integral
one is invertible by integral smooth base change
(`ProEtale.CondensedRing.isIso_baseChangeMap_app_padicIntegers_of_smooth`), the geometric generic
fibre being noetherian and `Lε^* K₀` bounded constructible. -/
theorem isIso_baseChangeMap_affineSpace_deformationModel_app {Y : Over (Spec (.of k))}
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (I : Y.left.IdealSheafData) (n : ℕ)
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left))}
    (hK : boundedConstructible _ K) :
    IsIso ((baseChangeMap (Profinite.padicAlgClRingObj ℓ)
      (IsPullback.of_hasPullback (deformationModel Y I k').j
        (𝔸(ULift.{u} (Fin n); (deformationModel Y I k').total) ↘
          (deformationModel Y I k').total)).toCommSq).app
      ((L(((deformationModel Y I k').ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K)) := by
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : IsNoetherian Y.left := ⟨⟩
  have := isNoetherian_deformationGeneric k' I
  have : CompactSpace (deformationModel Y I k').total :=
    QuasiCompact.compactSpace_of_compactSpace (deformationTotalToTrait Y I k')
  have : QuasiSeparatedSpace (deformationModel Y I k').total :=
    quasiSeparatedSpace_of_quasiSeparated (deformationTotalToTrait Y I k')
  have : QuasiCompact (deformationModel Y I k').j :=
    inferInstanceAs (QuasiCompact (pullback.fst (deformationTotalToTrait Y I k')
      (traitGenericPoint k')))
  have : QuasiSeparated (deformationModel Y I k').j :=
    inferInstanceAs (QuasiSeparated (pullback.fst (deformationTotalToTrait Y I k')
      (traitGenericPoint k')))
  have := AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin n))
    (deformationModel Y I k').total
  have : Smooth (𝔸(ULift.{u} (Fin n); (deformationModel Y I k').total) ↘
      (deformationModel Y I k').total) := 
    SmoothOfRelativeDimension.smooth (Nat.card (ULift.{u} (Fin n))) _
  have : CompactSpace 𝔸(ULift.{u} (Fin n); (deformationModel Y I k').total) :=
    QuasiCompact.compactSpace_of_compactSpace
      (𝔸(ULift.{u} (Fin n); (deformationModel Y I k').total) ↘ (deformationModel Y I k').total)
  have : QuasiSeparatedSpace 𝔸(ULift.{u} (Fin n); (deformationModel Y I k').total) :=
    quasiSeparatedSpace_of_quasiSeparated
      (𝔸(ULift.{u} (Fin n); (deformationModel Y I k').total) ↘ (deformationModel Y I k').total)
  have : CompactSpace ↥(pullback (deformationModel Y I k').j
      (𝔸(ULift.{u} (Fin n); (deformationModel Y I k').total) ↘
        (deformationModel Y I k').total)) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst _ _)
  have : QuasiSeparatedSpace ↥(pullback (deformationModel Y I k').j
      (𝔸(ULift.{u} (Fin n); (deformationModel Y I k').total) ↘
        (deformationModel Y I k').total)) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst _ _)
  have hℓ : IsUnit (ℓ : Γ((deformationModel Y I k').total, ⊤)) := by
    have hk : IsUnit (ℓ : k) := by
      refine IsUnit.mk0 _ fun h ↦ (Fact.out : ringChar k ≠ ℓ) ?_
      exact (Nat.prime_dvd_prime_iff_eq (Fact.out : (ringChar k).Prime) Fact.out).1
        ((ringChar.spec k ℓ).1 h)
    simpa using (hk.map (ΓSpecIso (.of k)).inv.hom).map
      (deformationTotalToBase Y I k' ≫ Y.hom).appTop.hom
  obtain ⟨E, K₀, ⟨e⟩⟩ := ProEtale.exists_padicAlgCl_iso_integralModel Y.left ℓ ⟨K, hK⟩
  have hM₀ := boundedConstructible_leftDerivedUpperStar_obj_of_scheme
    (Profinite.padicIntegersRingObj ℓ E.1) (deformationModel Y I k').ε K₀.obj K₀.property
  have h₀ := isIso_baseChangeMap_app_padicIntegers_of_smooth ℓ E
    (𝔸(ULift.{u} (Fin n); (deformationModel Y I k').total) ↘ (deformationModel Y I k').total)
    (IsPullback.of_hasPullback (deformationModel Y I k').j _) hℓ _ hM₀
  have : ((L(((deformationModel Y I k').ε)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj
      K₀.obj).IsGE hM₀.1.1.choose := hM₀.1.1.choose_spec
  have h₁ := isIso_baseChangeMap_app_padicAlgCl_of_padicIntegers ℓ E
    (IsPullback.of_hasPullback (deformationModel Y I k').j
      (𝔸(ULift.{u} (Fin n); (deformationModel Y I k').total) ↘
        (deformationModel Y I k').total)).toCommSq _ hM₀.1.1.choose this h₀
  sorry

/-- **The smooth exchange of nearby cycles** (blueprint `det-sp-nearby-cycles-exchanges` (1),
smooth case, for the morphism of deformation models of blueprint `det-sp-dnc-base-change` (3);
SGA 7 XIII 2.1.7.1): for a morphism `φ : 𝒟_J X ⟶ 𝒟_I Y` of deformation models whose morphism of
total spaces is smooth and whose square of geometric generic fibres is cartesian (for instance the
deformation of a smooth `f` with `J = f⁻¹ I`), the pullback exchange `α_φ : Lg_s^* Ψ_Y ⟶ Ψ_X Lg^*`
is an isomorphism on bounded constructible `ℚ̄_ℓ`-complexes, by smooth base change along the
inclusion `j` of the geometric generic fibre. -/
theorem isIso_pullbackExchange_deformationModel_app_of_smooth {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    {I : Y.left.IdealSheafData} {J : X.left.IdealSheafData} {g : X.left ⟶ Y.left}
    {g' : (deformationSpecialFibre X J k').left ⟶ (deformationSpecialFibre Y I k').left}
    (φ : (deformationModel X J k').Hom (deformationModel Y I k') g g') [Smooth φ.total]
    (hj : IsPullback φ.generic (deformationModel X J k').j (deformationModel Y I k').j φ.total)
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left))}
    (hK : boundedConstructible _ K) :
    IsIso ((φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app K) := by
  have : CompactSpace (deformationModel X J k').total :=
    QuasiCompact.compactSpace_of_compactSpace (deformationTotalToTrait X J k')
  have : QuasiSeparatedSpace (deformationModel X J k').total :=
    quasiSeparatedSpace_of_quasiSeparated (deformationTotalToTrait X J k')
  have hA (n : ℕ) := isIso_baseChangeMap_affineSpace_deformationModel_app k' I n hK
  have h₁ := φ.isIso_pullbackExchange_app_of_isIso_baseChangeMap_app
    (Profinite.padicAlgClRingObj ℓ) K
  have h₂ := isIso_baseChangeMap_app_of_smooth (Profinite.padicAlgClRingObj ℓ) hj
    ((L(((deformationModel Y I k').ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K)
  rw [Subsingleton.elim hj.toCommSq φ.commSq_j] at h₂
  revert hA h₁ h₂
  normalize_precoherent
  intro hA h₁ h₂
  exact h₁ (h₂ hA)

end AlgebraicGeometry.ProEtale.CondensedRing
