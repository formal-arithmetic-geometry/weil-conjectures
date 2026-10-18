/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeExchange.BaseChangeMap
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeExchange.OpenImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeExchange.Compactification

/-!
# Coefficient comparisons and the compact-support exchange map

We reduce the compatibility of the coefficient comparison
`AlgebraicGeometry.Etale.derivedRestrictScalarsCompRightDerivedLowerShriekIso` with the
compact-support exchange map `AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap`
to the compatibility of each of its building blocks, through the abstract predicate
`AlgebraicGeometry.Etale.CoeffCompatible` and its stability under composition, whiskering and
inversion. The building blocks (A), (B), (C) are not proved yet. The file then deduces the
coefficient-change statements used by `AlgebraicGeometry.Etale.AdicSystem`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')

section Exchange

variable [Finite Λ] [Finite Λ'] {X Y : Scheme.{u}} {f : X ⟶ Y} [CompactSpace Y]

/-- The isomorphism between the derived lower shrieks of two compactifications is compatible
with the coefficient comparisons. -/
lemma coeffCompatible_rightDerivedLowerShriekOfCompactificationIso [QuasiCompact f]
    (c d : Compactification f) :
    CoeffCompatible (compactificationRestrictScalarsIso ρ c)
      (compactificationRestrictScalarsIso ρ d)
      (rightDerivedLowerShriekOfCompactificationIso Λ c d).hom
      (rightDerivedLowerShriekOfCompactificationIso Λ' c d).hom :=
  (coeffCompatible_rightDerivedLowerShriekOfCompactificationComparison ρ _ _).comp
    (CoeffCompatible.inv (e := asIso _) (e' := asIso _)
      (coeffCompatible_rightDerivedLowerShriekOfCompactificationComparison ρ _ _))

end Exchange

section BaseChangeMap

variable [Finite Λ] [Finite Λ'] {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} [CompactSpace Y] [CompactSpace Y']

omit [Finite Λ'] in
/-- The compactly supported base change map along a compactification is compatible with the
coefficient comparisons, by (A) and (B). -/
lemma coeffCompatible_rightDerivedLowerShriekOfCompactificationBaseChangeMap
    (sq : IsPullback g' f' f g) (c : Compactification f) :
    CoeffCompatible
      (pasteTwoSquaresIso (compactificationRestrictScalarsIso ρ c)
        (leftDerivedUpperStarRestrictScalarsIso ρ g))
      (pasteTwoSquaresIso (leftDerivedUpperStarRestrictScalarsIso ρ g')
        (compactificationRestrictScalarsIso ρ (c.ofIsPullback sq)))
      (rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} Λ) sq c)
      (rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} Λ') sq c) := by
  have := c.isProper
  have := c.isOpenImmersion
  have := (c.ofIsPullback sq).isProper
  have := (c.ofIsPullback sq).isOpenImmersion
  exact (CoeffCompatible.associator_hom _ _ _).comp
    ((CoeffCompatible.whiskerLeft _
      (coeffCompatible_derivedBaseChangeMap ρ _ _ _ _ _)).comp
    ((CoeffCompatible.associator_inv _ _ _).comp
    ((CoeffCompatible.whiskerRight _ (CoeffCompatible.inv
      (coeffCompatible_derivedOpenImmersionLowerShriekBaseChangeIso ρ
        (c.isPullback_i_ofIsPullback sq)))).comp
    (CoeffCompatible.associator_hom _ _ _))))

/-- The compact-support exchange map is compatible with the coefficient comparisons. -/
lemma coeffCompatible_rightDerivedLowerShriekBaseChangeMap [HasCompactification f]
    [HasCompactification f'] [QuasiCompact f'] (sq : IsPullback g' f' f g) :
    CoeffCompatible
      (pasteTwoSquaresIso (derivedRestrictScalarsCompRightDerivedLowerShriekIso ρ f)
        (leftDerivedUpperStarRestrictScalarsIso ρ g))
      (pasteTwoSquaresIso (leftDerivedUpperStarRestrictScalarsIso ρ g')
        (derivedRestrictScalarsCompRightDerivedLowerShriekIso ρ f'))
      (rightDerivedLowerShriekBaseChangeMap Λ sq) (rightDerivedLowerShriekBaseChangeMap Λ' sq) :=
  (coeffCompatible_rightDerivedLowerShriekOfCompactificationBaseChangeMap ρ sq _).comp
    (CoeffCompatible.whiskerLeft _ (coeffCompatible_rightDerivedLowerShriekOfCompactificationIso
      ρ _ (HasCompactification.compactification f')))

end BaseChangeMap

variable [Finite Λ] [Finite Λ'] {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
  (aX : X ⟶ Spec (.of k)) [HasCompactification aX]

omit [IsSepClosed k] in
/-- The coefficient comparison of `Ra_!` is compatible with the compact-support exchange map
along an automorphism pair `(g, h)`. -/
lemma derivedRestrictScalarsCompRightDerivedLowerShriekIso_baseChangeMap [QuasiCompact aX]
    {g : X ⟶ X} {h : Spec (.of k) ⟶ Spec (.of k)} (sq : IsPullback g aX aX h)
    (K' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))) :
    (L((h)^*[ModuleCat.{u + 1} Λ])).map
        ((derivedRestrictScalarsCompRightDerivedLowerShriekIso ρ aX).hom.app K') ≫
      (leftDerivedUpperStarRestrictScalarsIso ρ h).hom.app
        ((R(aX)_![ModuleCat.{u + 1} Λ']).obj K') ≫
      (Sheaf.derivedRestrictScalars _ ρ).map
        ((rightDerivedLowerShriekBaseChangeMap Λ' sq).app K') =
    (rightDerivedLowerShriekBaseChangeMap Λ sq).app
        ((Sheaf.derivedRestrictScalars _ ρ).obj K') ≫
      (R(aX)_![ModuleCat.{u + 1} Λ]).map
        ((leftDerivedUpperStarRestrictScalarsIso ρ g).hom.app K') ≫
      (derivedRestrictScalarsCompRightDerivedLowerShriekIso ρ aX).hom.app
        ((L((g)^*[ModuleCat.{u + 1} Λ'])).obj K') := by
  simpa [pasteTwoSquaresIso_hom_app] using
    coeffCompatible_rightDerivedLowerShriekBaseChangeMap ρ sq K'


omit [IsSepClosed k] in
/-- The components of the compact-support base change `AlgebraicGeometry.Etale.compactPullback`. -/
lemma compactPullback_app {g : X ⟶ X} {h : Spec (.of k) ⟶ Spec (.of k)} [QuasiCompact aX]
    (sq : IsPullback g aX aX h) [IsIso h]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (compactPullback Λ sq).app K =
      (globalSectionsTransport Λ h).hom.app ((R(aX)_![ModuleCat.{u + 1} Λ]).obj K) ≫
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).map
          ((rightDerivedLowerShriekBaseChangeMap Λ sq).app K) := by
  simp [compactPullback]

/-- The coefficient comparison of compact cohomology is compatible with the compact-support base
change along every automorphism pair. -/
lemma isCompactPullbackCompatible_compactlySupportedGlobalSectionsRestrictScalarsIso
    [QuasiCompact aX] {g : X ⟶ X} {h : Spec (.of k) ⟶ Spec (.of k)}
    (sq : IsPullback g aX aX h) [IsIso h] :
    IsCompactPullbackCompatible ρ (compactlySupportedGlobalSectionsRestrictScalarsIso ρ aX) sq := by
  intro K'
  rw [compactPullback_app, compactPullback_app]
  exact pasteTwoSquaresIso_hom_app_comp_map_of_comm
    (α₁ := derivedRestrictScalarsCompRightDerivedLowerShriekIso ρ aX)
    (α₂ := derivedRestrictScalarsCompRightDerivedGlobalSectionsIso ρ)
    (εg := leftDerivedUpperStarRestrictScalarsIso ρ g)
    (εh := leftDerivedUpperStarRestrictScalarsIso ρ h)
    (Ex := rightDerivedLowerShriekBaseChangeMap Λ sq)
    (Ex' := rightDerivedLowerShriekBaseChangeMap Λ' sq)
    (T := (globalSectionsTransport Λ h).hom) (T' := (globalSectionsTransport Λ' h).hom)
    (derivedRestrictScalarsCompRightDerivedGlobalSectionsIso_hom_app_globalSectionsTransport ρ h)
    (derivedRestrictScalarsCompRightDerivedLowerShriekIso_baseChangeMap ρ aX sq) K'

/-- Blueprint `lem-fix-compact-support-coefficient-change` (subsection
`sk-def-sfb-coefficient-comparisons`): for a surjection `ρ : Λ →+* Λ'` of finite rings whose
exponent is invertible on the separably closed field `k` and a separated finite-type
`a_X : X ⟶ Spec k`, the canonical coefficient comparison
`RΓ_c(X, K) ⊗ᴸ_Λ Λ' ⟶ RΓ_c(X, K ⊗ᴸ_Λ Λ')`
(`AlgebraicGeometry.Etale.compactlySupportedGlobalSectionsRestrictScalarsIso`) is an
isomorphism for every `K ∈ Dᵇctf(X, Λ)`. -/
theorem isCoefficientChange_compactlySupportedGlobalSectionsRestrictScalarsIso [IsSeparated aX]
    [LocallyOfFiniteType aX] [QuasiCompact aX] [HasInvertibleExponent Λ (Spec (.of k))]
    (hρ : Function.Surjective ρ) :
    IsCoefficientChange ρ (compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX)
      (compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ') aX)
      (compactlySupportedGlobalSectionsRestrictScalarsIso ρ aX) :=
  sorry

variable [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX]


/-- Blueprint `lem-fix-compact-support-coefficient-change` (subsection
`sk-def-sfb-coefficient-comparisons`):
compact cohomology commutes with finite-level coefficient reduction, compatibly with pullback.
For a surjection `ρ : Λ →+* Λ'` of finite coefficient rings whose exponent is invertible on the
separably closed field `k` and a separated finite-type `a_X : X ⟶ Spec k`, compact cohomology
commutes with restriction of scalars along `ρ` through a coefficient comparison `α` for which
`RΓ_c(X, K) ⊗ᴸ_Λ Λ' ⟶ RΓ_c(X, K ⊗ᴸ_Λ Λ')` is an isomorphism for every `K ∈ Dᵇctf(X, Λ)`, and `α`
is compatible with the compact-support base change along every pair of automorphisms
(`AlgebraicGeometry.Etale.IsCompactPullbackCompatible`). -/
theorem exists_isCoefficientChange_compactlySupportedGlobalSections
    [HasInvertibleExponent Λ (Spec (.of k))] (hρ : Function.Surjective ρ) :
    ∃ α, IsCoefficientChange ρ (compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX)
        (compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ') aX) α ∧
      ∀ (g : X ⟶ X) (h : Spec (.of k) ⟶ Spec (.of k)) (sq : IsPullback g aX aX h) [IsIso h],
        IsCompactPullbackCompatible ρ α sq :=
  ⟨compactlySupportedGlobalSectionsRestrictScalarsIso ρ aX,
    isCoefficientChange_compactlySupportedGlobalSectionsRestrictScalarsIso ρ aX hρ,
    fun _ _ sq _ ↦
      isCompactPullbackCompatible_compactlySupportedGlobalSectionsRestrictScalarsIso ρ aX sq⟩

/-- Blueprint `thm-trf-finite-coefficient-map` (subsection `sk-p-trace-coeff`), the pullback
isomorphism at a geometric point: geometric stalks commute with finite-level coefficient
reduction, compatibly with the stalk transports. For a surjection `ρ : Λ →+* Λ'` of finite
coefficient rings whose exponent is invertible on `k` and a geometric point `x̄ : Spec k ⟶ X`,
the geometric stalk commutes with restriction of scalars along `ρ` through a coefficient
comparison `β` for which `K_x̄ ⊗ᴸ_Λ Λ' ⟶ (K ⊗ᴸ_Λ Λ')_x̄` is an isomorphism for every
`K ∈ Dᵇctf(X, Λ)`, and `β` is compatible with the stalk transport at `x̄` along every pair of
automorphisms fixing `x̄` (`AlgebraicGeometry.Etale.IsStalkPullbackCompatible`). -/
theorem exists_isCoefficientChange_geometricStalk
    [HasInvertibleExponent Λ (Spec (.of k))] (hρ : Function.Surjective ρ)
    (x : Spec (.of k) ⟶ X) :
    ∃ β, IsCoefficientChange ρ (geometricStalk Λ x) (geometricStalk Λ' x) β ∧
      ∀ (g : X ⟶ X) (h : Spec (.of k) ⟶ Spec (.of k)) (hx : h ≫ x = x ≫ g) [IsIso h],
        IsStalkPullbackCompatible ρ β hx :=
  ⟨geometricStalkRestrictScalarsIso ρ x,
    isCoefficientChange_geometricStalkRestrictScalarsIso ρ x hρ,
    fun _ _ hx _ ↦ isStalkPullbackCompatible_geometricStalkRestrictScalarsIso ρ x hx⟩

namespace AdicSystem

variable {R : Type (u + 1)} [CommRing R] {I : Ideal R} (S : AdicSystem I X)
  [∀ n, Finite (R ⧸ I ^ n)] [∀ n, HasInvertibleExponent (R ⧸ I ^ n) (Spec (.of k))]

include aX in
/-- Blueprint `prop-trf-adic-coefficient-morphism-systems` (1), levelwise perfectness and
normalization: each `P_n = RΓ_c(X, L_n)` and each geometric stalk `P_{x̄, n} = (L_n)_x̄` is a
perfect complex of `A_n`-modules, and the transition `ν_n` induces, through an identification of
`RΓ_c(X, -)` (resp. `(-)_x̄`) of a restriction of scalars with the restriction of scalars of
`RΓ_c(X, -)` (resp. `(-)_x̄`), a map `P_{n+1} ⟶ Res P_n` exhibiting `P_n` as
`P_{n+1} ⊗ᴸ_{A_{n+1}} A_n`, i.e. an isomorphism `P_{n+1} ⊗ᴸ_{A_{n+1}} A_n ≅ P_n`. -/
theorem isPerfect_and_exists_isDerivedBaseChange (n : ℕ) :
    ((compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ n)) aX).obj
        (S.obj n)).IsPerfect ∧
      (∃ e : (compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))) aX).obj
          ((_root_.DerivedCategory.levelTransitionRestrictScalars _ I n.le_succ).obj (S.obj n)) ≅
          (ModuleCat.derivedRestrictScalars
            (Ideal.Quotient.factor (Ideal.pow_le_pow_right n.le_succ))).obj
            ((compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ n)) aX).obj
              (S.obj n)),
        ModuleCat.IsDerivedBaseChange
          ((compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))) aX).map
            (S.map n) ≫ e.hom)) ∧
      ∀ x : Spec (.of k) ⟶ X,
        ((geometricStalk (R ⧸ I ^ n) x).obj (S.obj n)).IsPerfect ∧
        ∃ e : (geometricStalk (R ⧸ I ^ (n + 1)) x).obj
            ((_root_.DerivedCategory.levelTransitionRestrictScalars _ I n.le_succ).obj
              (S.obj n)) ≅
            (ModuleCat.derivedRestrictScalars
              (Ideal.Quotient.factor (Ideal.pow_le_pow_right n.le_succ))).obj
              ((geometricStalk (R ⧸ I ^ n) x).obj (S.obj n)),
          ModuleCat.IsDerivedBaseChange
            ((geometricStalk (R ⧸ I ^ (n + 1)) x).map (S.map n) ≫ e.hom) := by
  have hsurj : Function.Surjective
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := I) n.le_succ)) :=
    Ideal.Quotient.factor_surjective _
  refine ⟨isPerfect_compactlySupportedGlobalSections _ aX _ (S.boundedConstructibleFiniteTor n),
    ?_, fun x ↦ ⟨isPerfect_geometricStalk _ x _ (S.boundedConstructibleFiniteTor n), ?_⟩⟩
  · obtain ⟨α, hα, -⟩ := exists_isCoefficientChange_compactlySupportedGlobalSections _ aX hsurj
    exact ⟨α.app _, hα _ (S.boundedConstructibleFiniteTor (n + 1)) (S.isDerivedBaseChange n)⟩
  · obtain ⟨β, hβ, -⟩ := exists_isCoefficientChange_geometricStalk _ hsurj x
    exact ⟨β.app _, hβ _ (S.boundedConstructibleFiniteTor (n + 1)) (S.isDerivedBaseChange n)⟩

include aX in
/-- The coefficient identifications from which
`AlgebraicGeometry.Etale.AdicSystem.compactSupportTower` is built exist, compatibly with the
compact-support base change along every pair of automorphisms
(`AlgebraicGeometry.Etale.exists_isCoefficientChange_compactlySupportedGlobalSections`). -/
lemma exists_compactSupportTower :
    ∃ (α : ∀ n : ℕ, Sheaf.derivedRestrictScalars X.smallEtaleTopology (I.powSuccFactor n) ⋙
        compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1 + 1))) aX ≅
      compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))) aX ⋙
        ModuleCat.derivedRestrictScalars (I.powSuccFactor n)),
      (∀ n : ℕ, IsCoefficientChange (I.powSuccFactor n) _ _ (α n)) ∧
      ∀ (n : ℕ) (g : X ⟶ X) (h : Spec (.of k) ⟶ Spec (.of k)) (sq : IsPullback g aX aX h)
        [IsIso h], IsCompactPullbackCompatible (I.powSuccFactor n) (α n) sq := by
  choose α hα hα' using fun n : ℕ ↦ exists_isCoefficientChange_compactlySupportedGlobalSections
    (I.powSuccFactor n) aX (Ideal.Quotient.factor_surjective _)
  exact ⟨α, hα, hα'⟩

/-- The coefficient identifications from which `AlgebraicGeometry.Etale.AdicSystem.stalkTower`
is built exist, compatibly with the stalk transports
(`AlgebraicGeometry.Etale.exists_isCoefficientChange_geometricStalk`). -/
lemma exists_stalkTower (x : Spec (.of k) ⟶ X) :
    ∃ (β : ∀ n : ℕ, Sheaf.derivedRestrictScalars X.smallEtaleTopology (I.powSuccFactor n) ⋙
        geometricStalk (R ⧸ I ^ (n + 1 + 1)) x ≅
      geometricStalk (R ⧸ I ^ (n + 1)) x ⋙ ModuleCat.derivedRestrictScalars (I.powSuccFactor n)),
      (∀ n : ℕ, IsCoefficientChange (I.powSuccFactor n) _ _ (β n)) ∧
      ∀ (n : ℕ) (g : X ⟶ X) (h : Spec (.of k) ⟶ Spec (.of k)) (hx : h ≫ x = x ≫ g)
        [IsIso h], IsStalkPullbackCompatible (I.powSuccFactor n) (β n) hx := by
  choose β hβ hβ' using fun n : ℕ ↦ exists_isCoefficientChange_geometricStalk
    (I.powSuccFactor n) (Ideal.Quotient.factor_surjective _) x
  exact ⟨β, hβ, hβ'⟩

end AdicSystem

end AlgebraicGeometry.Etale
