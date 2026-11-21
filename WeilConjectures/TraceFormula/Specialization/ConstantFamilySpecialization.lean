/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.Specialization
public import WeilConjectures.TraceFormula.Specialization.DefectExchanges
public import WeilConjectures.TraceFormula.Specialization.DeformationSpecialFibreBaseChange
public import WeilConjectures.TraceFormula.Specialization.ThickOriginReducedUnit

/-!

# The specialization map of a constant family

For a `k`-scheme `Y`, the constant family `Y × S` over the trait `S = Spec k'⟦t⟧` is the
deformation of the zero ideal of `Y` (`ProEtale.CondensedRing.deformationModel Y ⊥ k'`). Its
special fibre is `Y ⊗ k'`, with projection `π_Y : Y ⊗ k' ⟶ Y`
(`ProEtale.CondensedRing.constantSpecialFibreProj`), and the projection `Y × S ⟶ Y` of its total
space restricts to the identification of the geometric generic fibre. The *specialization map*
```
σ_Y(L) : Lπ_Y^* L ⟶ Ψ_{Y × S}(L)
```
(`ProEtale.CondensedRing.constantFamilySpecialization`) is the restriction to the special fibre
of the unit of `Lj^* ⊣ Rj_*`, for `j` the inclusion of the geometric generic fibre.

## Main results

- `ProEtale.CondensedRing.constantFamilySpecialization_app_comp_pushforwardExchange_app`: for
  `f : Y' ⟶ Y`, the pushforward exchange carries `σ_Y(Rf_* L')` to `Rf_{s*} σ_{Y'}(L')`,
  composed with the base change map `Lπ_Y^* Rf_* ⟶ Rf_{s*} Lπ_{Y'}^*`.
- `ProEtale.CondensedRing.map_constantFamilySpecialization_app_comp_pullbackExchange_app`: for
  `f : Y' ⟶ Y`, the pullback exchange carries `Lf_s^* σ_Y(L)` to `σ_{Y'}(Lf^* L)`.
- `ProEtale.CondensedRing.isIso_constantFamilySpecialization_app`: for `Y` separated of finite
  type over `k` and `L` bounded constructible with `ℚ̄_ℓ`-coefficients, `σ_Y(L)` is an
  isomorphism.
- `ProEtale.CondensedRing.isIso_constantFamilySpecialization_app_upperStar_iff_of_smooth`,
  `ProEtale.CondensedRing.isIso_constantFamilySpecialization_app_lowerStar_iff_of_isProper`:
  whether `σ` is invertible is compatible with smooth pullback and with proper direct image.

## Implementation details

The isomorphism `isIso_constantFamilySpecialization_app` is reduced to affine spaces: the
question is local for a finite affine open cover (smooth pullback), and an affine `Y` embeds into
some `𝔸ⁿ_k` by a closed immersion `i`, along which `Ri_{s*}` reflects isomorphisms (proper direct
image). The case of affine space, `isIso_constantFamilySpecialization_app_affineSpaceOver`, is not
proved yet.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k] (k' : Type u) [Field k'] [Algebra k k']
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The projection `𝒳 ⟶ X` of the total space of the deformation restricts to the identification
`ε : 𝒳_η̄ ⟶ X` of the geometric generic fibre. -/
lemma deformationModel_j_comp_deformationTotalToBase {X : Over (Spec (.of k))}
    (I : X.left.IdealSheafData) :
    (deformationModel X I k').j ≫ deformationTotalToBase X I k' = (deformationModel X I k').ε := by
  rw [deformationModel_j, deformationModel_ε]

/-- The projection `𝒳 ⟶ Y` of the total space of the constant family restricts to the projection
`π_Y : Y ⊗ k' ⟶ Y` of the special fibre. -/
lemma deformationModel_i_comp_deformationTotalToBase (Y : Over (Spec (.of k))) :
    (deformationModel Y ⊥ k').i ≫ deformationTotalToBase Y ⊥ k' = constantSpecialFibreProj k' Y :=
  rfl

/-- The *specialization map* `σ_Y : Lπ_Y^* ⟶ Ψ_{Y × S}` of the constant family `Y × S` of a
`k`-scheme `Y` over the trait `S = Spec k'⟦t⟧`, where `π_Y : Y ⊗ k' ⟶ Y` is the projection from
the special fibre: the restriction to the special fibre of the unit of `Lj^* ⊣ Rj_*`. -/
noncomputable def constantFamilySpecialization (Y : Over (Spec (.of k))) :
    L((constantSpecialFibreProj k' Y)^*⟦Λ⟧) ⟶ (deformationModel Y ⊥ k').nearbyCycles Λ :=
  (deformationModel Y ⊥ k').specialization Λ (deformationTotalToBase Y ⊥ k')
    (deformationModel_j_comp_deformationTotalToBase k' ⊥)
    (deformationModel_i_comp_deformationTotalToBase k' Y)

variable {A B : Over (Spec (.of k))} (g : A ⟶ B)
  (hg : ∀ ⦃U' : A.left.AffineZariskiSite⦄ ⦃U : B.left.AffineZariskiSite⦄
    (hU : U'.1 ≤ g.left ⁻¹ᵁ U.1), ((⊥ : B.left.IdealSheafData).siteIdeal U).map
      (g.left.appLE U.1 U'.1 hU).hom ≤ (⊥ : A.left.IdealSheafData).siteIdeal U')

/-- The morphism of total spaces of `g̃ : 𝒟_⊥ A ⟶ 𝒟_⊥ B` lies over `g`. -/
lemma deformationModelHom_total_comp_deformationTotalToBase :
    (deformationModelHom g hg k').total ≫ deformationTotalToBase B ⊥ k' =
      deformationTotalToBase A ⊥ k' ≫ g.left := by
  rw [deformationModelHom_total, deformationTotalMap_toBase]

/-- The square `π_A ≫ g = g_s ≫ π_B` of special fibres of constant families. -/
lemma commSq_constantSpecialFibreProj :
    CommSq (constantSpecialFibreProj k' A) (deformationSpecialFibreMap g hg k').left g.left
      (constantSpecialFibreProj k' B) :=
  (isPullback_deformationSpecialFibreMap_bot k' g hg).flip.toCommSq

/-- **The specialization map and proper direct image**: for `g : A ⟶ B`, the pushforward
exchange `χ_g : Ψ_B Rg_* ⟶ Rg_{s*} Ψ_A` carries `σ_B(Rg_* E)` to `Rg_{s*} σ_A(E)`, composed with
the base change map `Lπ_B^* Rg_* ⟶ Rg_{s*} Lπ_A^*`. -/
theorem constantFamilySpecialization_app_comp_pushforwardExchange_app
    (E : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology A.left) Ab.{u + 1})
      (condensedRingObj Λ A.left))) :
    (constantFamilySpecialization k' Λ B).app (R((g.left)_*⟦Λ⟧).obj E) ≫
        ((deformationModelHom g hg k').pushforwardExchange Λ).app E =
      (baseChangeMap Λ (commSq_constantSpecialFibreProj k' g hg)).app E ≫
        R(((deformationSpecialFibreMap g hg k').left)_*⟦Λ⟧).map
          ((constantFamilySpecialization k' Λ A).app E) :=
  (deformationModelHom g hg k').specialization_app_comp_pushforwardExchange_app Λ
    (deformationModel_j_comp_deformationTotalToBase k' ⊥)
    (deformationModel_j_comp_deformationTotalToBase k' ⊥)
    (deformationModel_i_comp_deformationTotalToBase k' A)
    (deformationModel_i_comp_deformationTotalToBase k' B)
    (deformationModelHom_total_comp_deformationTotalToBase k' g hg)
    (commSq_constantSpecialFibreProj k' g hg) E

/-- **The specialization map and pullback**: for `g : A ⟶ B`, the pullback exchange
`α_g : Lg_s^* Ψ_B ⟶ Ψ_A Lg^*` carries `Lg_s^* σ_B(K)` to `σ_A(Lg^* K)`, up to the pullback
comparison `Lg_s^* Lπ_B^* ≅ Lπ_A^* Lg^*`. -/
theorem map_constantFamilySpecialization_app_comp_pullbackExchange_app
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B.left) Ab.{u + 1})
      (condensedRingObj Λ B.left))) :
    L(((deformationSpecialFibreMap g hg k').left)^*⟦Λ⟧).map
        ((constantFamilySpecialization k' Λ B).app K) ≫
        ((deformationModelHom g hg k').pullbackExchange Λ).app K =
      (pullbackSquareComparison Λ (commSq_constantSpecialFibreProj k' g hg)).hom.app K ≫
        (constantFamilySpecialization k' Λ A).app (L((g.left)^*⟦Λ⟧).obj K) :=
  (deformationModelHom g hg k').map_specialization_app_comp_pullbackExchange_app Λ
    (deformationModel_j_comp_deformationTotalToBase k' ⊥)
    (deformationModel_j_comp_deformationTotalToBase k' ⊥)
    (deformationModel_i_comp_deformationTotalToBase k' A)
    (deformationModel_i_comp_deformationTotalToBase k' B)
    (deformationModelHom_total_comp_deformationTotalToBase k' g hg)
    (commSq_constantSpecialFibreProj k' g hg) K

/-- In a commutative square `f ≫ α = β ≫ g` with `α` and `β` isomorphisms, `f` is an
isomorphism if and only if `g` is. -/
private lemma isIso_iff_of_comp_eq {C : Type*} [Category C] {a b c d : C} {f : a ⟶ b}
    {α : b ⟶ d} {β : a ⟶ c} {g : c ⟶ d} (h : f ≫ α = β ≫ g) (hα : IsIso α) (hβ : IsIso β) :
    IsIso f ↔ IsIso g := by
  rw [← isIso_comp_right_iff f α, h, isIso_comp_left_iff]

variable {ℓ : ℕ} [Fact ℓ.Prime] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [LocallyOfFiniteType A.hom] [QuasiCompact A.hom] [IsSeparated A.hom]
  [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]

/-- **Smooth pullback of the specialization map**: for `g : A ⟶ B` smooth and `K` bounded
constructible on `B`, `σ_A(Lg^* K)` is an isomorphism if and only if `Lg_s^* σ_B(K)` is. -/
theorem isIso_constantFamilySpecialization_app_upperStar_iff_of_smooth [Smooth g.left]
    (K : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((constantFamilySpecialization k' (Profinite.padicAlgClRingObj ℓ) A).app
        (L((g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj K.obj)) ↔
      IsIso (L(((deformationSpecialFibreMap g hg k').left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map
        ((constantFamilySpecialization k' (Profinite.padicAlgClRingObj ℓ) B).app K.obj)) := by
  have : Smooth (deformationModelHom g hg k').total :=
    smooth_deformationTotalMap k' g hg (IdealSheafData.comap_bot _).symm
  have hα := isIso_pullbackExchange_deformationModel_app_of_smooth k' (deformationModelHom g hg k')
    (isPullback_deformationGenericMap _ _ k') K.property
  have h := map_constantFamilySpecialization_app_comp_pullbackExchange_app k'
    (Profinite.padicAlgClRingObj ℓ) g hg K.obj
  revert hα h
  normalize_precoherent
  intro hα h
  exact (isIso_iff_of_comp_eq h hα inferInstance).symm

omit [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k).Prime] in
/-- **Proper direct image of the specialization map**: for `g : A ⟶ B` proper and `E` bounded
constructible on `A`, `σ_B(Rg_* E)` is an isomorphism if and only if `Rg_{s*} σ_A(E)` is. -/
theorem isIso_constantFamilySpecialization_app_lowerStar_iff_of_isProper [IsProper g.left]
    (E : Dᵇc(A.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((constantFamilySpecialization k' (Profinite.padicAlgClRingObj ℓ) B).app
        (R((g.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj E.obj)) ↔
      IsIso (R(((deformationSpecialFibreMap g hg k').left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).map
        ((constantFamilySpecialization k' (Profinite.padicAlgClRingObj ℓ) A).app E.obj)) := by
  have : IsProper (deformationModelHom g hg k').total :=
    isProper_deformationTotalMap k' g hg (IdealSheafData.comap_bot _).symm
  have := isNoetherian_of_locallyOfFiniteType B.hom
  have := isNoetherian_of_locallyOfFiniteType (deformationSpecialFibre B ⊥ k').hom
  have h₁ := (deformationModelHom g hg k').isIso_pushforwardExchange_app_of_isProper B.hom
    (isTraitModel_deformationModel _ _ k').exists_over
    (isTraitModel_deformationModel _ _ k').exists_over
    (isPullback_deformationSpecialFibreMap_toTotal g hg k').flip
    (isPullback_deformationModel_ε_deformationGenericMap k' g hg) E.property
  have h₂ := isIso_baseChangeMap_app_padicAlgCl_of_isProper ℓ B.hom
    (deformationSpecialFibre B ⊥ k').hom (commSq_constantSpecialFibreProj k' g hg)
    (isPullback_deformationSpecialFibreMap_bot k' g hg).flip E.obj E.property
  have h := constantFamilySpecialization_app_comp_pushforwardExchange_app k'
    (Profinite.padicAlgClRingObj ℓ) g hg E.obj
  revert h₁ h₂ h
  normalize_precoherent
  intro h₁ h₂ h
  exact isIso_iff_of_comp_eq h h₁ h₂

variable (ℓ) in
/-- **The constant family of affine space**: for `L` bounded constructible on `𝔸ⁿ_k`, the
specialization map `σ_{𝔸ⁿ}(L) : Lπ^* L ⟶ Ψ_{𝔸ⁿ × S}(L)` is an isomorphism. -/
theorem isIso_constantFamilySpecialization_app_affineSpaceOver (n : ℕ)
    (L : Dᵇc((affineSpaceOver k n).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((constantFamilySpecialization k' (Profinite.padicAlgClRingObj ℓ)
      (affineSpaceOver k n)).app L.obj) := by
  sorry

/-- **The constant family of an affine scheme**: for `Y` affine of finite type over `k` and `L`
bounded constructible on `Y`, `σ_Y(L)` is an isomorphism. -/
theorem isIso_constantFamilySpecialization_app_of_isAffine [IsAffine A.left]
    (L : Dᵇc(A.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((constantFamilySpecialization k' (Profinite.padicAlgClRingObj ℓ) A).app L.obj) := by
  let e := affineSpaceEmbedding A
  have hg := siteIdeal_bot_map_appLE_le e.i.left ⊥
  have h := isIso_constantFamilySpecialization_app_affineSpaceOver k' ℓ e.n
    ((boundedConstructibleLowerStar ℓ e.i).obj L)
  rw [show ((boundedConstructibleLowerStar ℓ e.i).obj L).obj =
    R((e.i.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj L.obj from rfl,
    isIso_constantFamilySpecialization_app_lowerStar_iff_of_isProper k' e.i hg L] at h
  have : IsClosedImmersion (deformationSpecialFibreMap e.i hg k').left :=
    MorphismProperty.of_isPullback (isPullback_deformationSpecialFibreMap_bot k' e.i hg).flip
      inferInstance
  exact ((derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ)
    (deformationSpecialFibreMap e.i hg k').left).fullyFaithfulROfIsIsoCounit).isIso_of_isIso_map _

/-- **Nearby cycles of a constant family**: for `Y` separated of finite type over `k` and `L`
bounded constructible on `Y`, the specialization map `σ_Y(L) : Lπ_Y^* L ⟶ Ψ_{Y × S}(L)` is an
isomorphism. -/
theorem isIso_constantFamilySpecialization_app (L : Dᵇc(A.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((constantFamilySpecialization k' (Profinite.padicAlgClRingObj ℓ) A).app L.obj) := by
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  choose U hU hxU _ using fun x : A.left ↦ exists_isAffineOpen_mem_and_subset
    (show x ∈ (⊤ : A.left.Opens) from trivial)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : A.left ↦ ((U x : A.left.Opens) :
    Set A.left)) (fun x ↦ (U x).isOpen) (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxU x⟩)
  let V (a : t) := overRestrict A (U a.1)
  let g (a : t) : V a ⟶ A := overRestrictι A (U a.1)
  have hg (a : t) := siteIdeal_bot_map_appLE_le (g a).left ⊥
  have hV (a : t) : IsAffine (V a).left := hU a.1
  have h (a : t) : IsIso (L(((deformationSpecialFibreMap (g a) (hg a) k').left)^*⟦
      Profinite.padicAlgClRingObj ℓ⟧).map
        ((constantFamilySpecialization k' (Profinite.padicAlgClRingObj ℓ) A).app L.obj)) := by
    rw [← isIso_constantFamilySpecialization_app_upperStar_iff_of_smooth k' (g a) (hg a) L]
    exact isIso_constantFamilySpecialization_app_of_isAffine k'
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (g a)).obj L)
  have (a : t) : QuasiCompact (deformationSpecialFibreMap (g a) (hg a) k').left :=
    MorphismProperty.of_isPullback (isPullback_deformationSpecialFibreMap_bot k' (g a) (hg a)).flip
      inferInstance
  have := h
  refine (jointlyReflectIsomorphisms_leftDerivedUpperStar_of_cover
    (Profinite.padicAlgClRingObj ℓ) (fun a ↦ (deformationSpecialFibreMap (g a) (hg a) k').left)
    fun p ↦ ?_).isIso _
  obtain ⟨x, hx, hpx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ (constantSpecialFibreProj k' A p)))
  refine ⟨⟨x, hx⟩, ?_⟩
  rw [Scheme.range_snd_of_isPullback
    (isPullback_deformationSpecialFibreMap_bot k' (g _) (hg _)).flip]
  change constantSpecialFibreProj k' A p ∈ Set.range (U x).ι.base
  rw [(U x).range_ι]
  exact hpx

end AlgebraicGeometry.ProEtale.CondensedRing
