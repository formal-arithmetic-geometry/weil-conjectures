/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.PerfectTower
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Adic

/-!
# Normalized adic systems and the realization of their compact cohomology

Let `R` be a ring with an ideal `I = (ϖ)` (the intended case being `R = 𝒪_E`, `I = 𝔪_E`) and
`A_n = R ⧸ Iⁿ`. A *normalized adic system* on a scheme `X` (`AlgebraicGeometry.ProEtale.AdicSystem`,
blueprint `def-trf-adic-system`) is a family `L_n ∈ Dᵇctf(X, A_n)` with transitions
`L_{n+1} ⟶ Res L_n` exhibiting `L_n` as `L_{n+1} ⊗ᴸ_{A_{n+1}} A_n`.

For a geometric scheme `a_X : X ⟶ s` over a separably closed field, the compact cohomology
complexes `P_n = RΓ_c(X, L_n) ∈ D(A_n)` and the geometric stalks `P_{x̄, n} = (L_n)_x̄` form
normalized towers of perfect complexes (blueprint `prop-trf-adic-coefficient-morphism-systems`
(1)), whose derived limits over `R` are therefore perfect, reduce to the levels, and carry lifts
of compatible families of endomorphisms whose traces are the limits of the levelwise traces
(`prop-trf-adic-coefficient-morphism-systems` (2), (4); `sk-prop-trace-adic` (ii)).

## Main definitions

- `AlgebraicGeometry.ProEtale.AdicSystem`: a normalized `A_•`-system.
- `AlgebraicGeometry.ProEtale.IsCoefficientChange`: a natural isomorphism
  `Res ∘ Φ ≅ Φ' ∘ Res` identifying `Φ'` of a derived base change with the derived base change
  of `Φ`.
- `AlgebraicGeometry.ProEtale.AdicSystem.compactSupportTower`,
  `AlgebraicGeometry.ProEtale.AdicSystem.stalkTower`: the normalized towers of perfect complexes
  `RΓ_c(X, L_n)` and `(L_n)_x̄`.

## Main results

- `AlgebraicGeometry.ProEtale.AdicSystem.isPerfect_and_exists_isDerivedBaseChange`: blueprint
  `prop-trf-adic-coefficient-morphism-systems` (1).
- `AlgebraicGeometry.ProEtale.AdicSystem.compactSupportTower_realization`,
  `AlgebraicGeometry.ProEtale.AdicSystem.stalkTower_realization`: blueprint
  `sk-prop-trace-adic` (ii), the perfect realizations.

## Implementation notes

The coefficient categories at the levels are `ModuleCat (R ⧸ Iⁿ)`, and the comparison between the
levels goes through restriction of scalars: compact cohomology with `A_{n+1}`-coefficients of the
restriction of an `A_n`-complex is identified with the restriction of its compact cohomology
with `A_n`-coefficients. This identification, and the fact that it carries derived base changes
of constructible complexes of finite Tor amplitude to derived base changes, is the finite-level
coefficient change of compact cohomology (`lem-fix-compact-support-coefficient-change`) and of
geometric stalks (`thm-trf-finite-coefficient-map`), stated here as
`AlgebraicGeometry.ProEtale.exists_isCoefficientChange_compactlySupportedGlobalSections` and
`AlgebraicGeometry.ProEtale.exists_isCoefficientChange_stalk`. The towers are built from any
such identifications, so that they are data independent of a choice.

Compact cohomology and geometric stalks are read in `D(A_n)` through the point identification
of blueprint `def-weil-finite-coefficient-point`: `RΓ_c(X, -)` is
`AlgebraicGeometry.ProEtale.compactlySupportedGlobalSections` and the geometric stalk at
`x̄ : s ⟶ X` is `RΓ(s, Lx̄^* -)`.

The levels of the system are indexed as in `AlgebraicGeometry.ProEtale.IsNormalizedTower`, by
`n : ℕ` with coefficients `R ⧸ Iⁿ`; the tower `n ↦ R ⧸ Iⁿ⁺¹` of local rings over which the towers
of perfect complexes live omits the zero ring `R ⧸ I⁰`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated MonoidalCategory

namespace AlgebraicGeometry.ProEtale

section CoefficientChange

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') {X : Scheme.{u}}

/-- A natural isomorphism `α : Res ∘ Φ ≅ Φ' ∘ Res` between functors
`Φ : D(X_proét, Λ) ⥤ D(Λ)` and `Φ' : D(X_proét, Λ') ⥤ D(Λ')`, along a ring map `ρ : Λ →+* Λ'`,
*is a coefficient change* if it carries derived base changes of bounded constructible complexes
of finite Tor amplitude to derived base changes: for `η : K ⟶ Res K'` exhibiting `K'` as
`K ⊗ᴸ_Λ Λ'`, the map `Φ K ⟶ Φ (Res K') ≅ Res (Φ' K')` exhibits `Φ' K'` as `Φ K ⊗ᴸ_Λ Λ'`. This is
the statement that the coefficient comparison `(Φ K) ⊗ᴸ_Λ Λ' ⟶ Φ' (K ⊗ᴸ_Λ Λ')` is an
isomorphism. -/
def IsCoefficientChange
    (Φ : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (ModuleCat.{u + 1} Λ))
    (Φ' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ')) ⥤
      DerivedCategory (ModuleCat.{u + 1} Λ'))
    (α : Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) ρ ⋙ Φ ≅
      Φ' ⋙ ModuleCat.derivedRestrictScalars ρ) : Prop :=
  ∀ ⦃K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))⦄
    ⦃K' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ'))⦄
    (η : K ⟶ (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) ρ).obj K'),
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
      Sheaf.IsDerivedBaseChange η → ModuleCat.IsDerivedBaseChange (Φ.map η ≫ α.hom.app K')

/-- The geometric stalk `K_x̄ = RΓ(s, Lx̄^* K) ∈ D(Λ)` at a point `x̄ : s ⟶ X`, read in `D(Λ)`
through the point identification of blueprint `def-weil-finite-coefficient-point`. -/
noncomputable abbrev geometricStalk (Λ : Type (u + 1)) [CommRing Λ] {s : Scheme.{u}}
    (x : s ⟶ X) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (ModuleCat.{u + 1} Λ) :=
  (upperStar (ModuleCat.{u + 1} Λ) x).leftDerivedFunctor ⋙
    rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) s

variable {k : Type u} [Field k] [IsSepClosed k] (aX : X ⟶ Spec (.of k)) [IsGeometric aX]
  [HasCompactification aX]

/-- Blueprint `sk-prop-sf-trace-perfectness` (`prop-trf-compact-support-perfectness`), in the
pro-étale setting: for a finite coefficient ring `Λ` whose exponent is invertible on the
separably closed field `k`, a separated finite-type `a_X : X ⟶ Spec k` and
`K ∈ Dᵇctf(X, Λ)`, compact cohomology `RΓ_c(X, K)` and every geometric stalk `K_x̄` are perfect
complexes of `Λ`-modules. -/
theorem isPerfect_compactlySupportedGlobalSections_obj [Finite Λ]
    [HasInvertibleExponent Λ (Spec (.of k))]
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX).obj K).IsPerfect ∧
      ∀ x : Spec (.of k) ⟶ X, x ≫ aX = 𝟙 _ → ((geometricStalk Λ x).obj K).IsPerfect :=
  sorry

/-- Blueprint `lem-fix-compact-support-coefficient-change`, read at the point through
`def-weil-finite-coefficient-point`: for a surjection `ρ : Λ →+* Λ'` of finite coefficient rings
whose exponent is invertible on `k` and a separated finite-type `a_X : X ⟶ Spec k`, compact
cohomology commutes with restriction of scalars along `ρ`, and the canonical coefficient
comparison `RΓ_c(X, K) ⊗ᴸ_Λ Λ' ⟶ RΓ_c(X, K ⊗ᴸ_Λ Λ')` is an isomorphism for `K ∈ Dᵇctf(X, Λ)`. -/
theorem exists_isCoefficientChange_compactlySupportedGlobalSections [Finite Λ] [Finite Λ']
    [HasInvertibleExponent Λ (Spec (.of k))] (hρ : Function.Surjective ρ) :
    ∃ α, IsCoefficientChange ρ (compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX)
      (compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ') aX) α :=
  sorry

/-- Blueprint `thm-trf-finite-coefficient-map` (the pullback isomorphism, at a geometric point,
read at the point through `def-weil-finite-coefficient-point`): for a surjection
`ρ : Λ →+* Λ'` of finite coefficient rings whose exponent is invertible on `k` and a geometric
point `x̄ : Spec k ⟶ X`, the geometric stalk commutes with restriction of scalars along `ρ`, and
the coefficient comparison `K_x̄ ⊗ᴸ_Λ Λ' ⟶ (K ⊗ᴸ_Λ Λ')_x̄` is an isomorphism for
`K ∈ Dᵇctf(X, Λ)`. -/
theorem exists_isCoefficientChange_stalk [Finite Λ] [Finite Λ']
    [HasInvertibleExponent Λ (Spec (.of k))] (hρ : Function.Surjective ρ)
    (x : Spec (.of k) ⟶ X) (hx : x ≫ aX = 𝟙 _) :
    ∃ α, IsCoefficientChange ρ (geometricStalk Λ x) (geometricStalk Λ' x) α :=
  sorry

end CoefficientChange

section AdicSystem

variable {R : Type (u + 1)} [CommRing R] (I : Ideal R) (X : Scheme.{u})

/-- Blueprint `def-trf-adic-system`: a *normalized `A_•`-system* on `X`, for the rings
`A_n = R ⧸ Iⁿ`: complexes `L_n ∈ Dᵇctf(X, A_n)` with transitions `L_{n+1} ⟶ Res L_n` compatible
with the quotient maps `A_{n+1} ⟶ A_n`, exhibiting `L_n` as `L_{n+1} ⊗ᴸ_{A_{n+1}} A_n`.

No Weil structure is part of the datum; the category `Dᵇctf,W,adic(X, 𝒪_E)` of the blueprint
consists of such systems with a compatible strict Weil structure at every level. -/
structure AdicSystem where
  /-- The level `L_n ∈ D(X, R ⧸ Iⁿ)`. -/
  obj (n : ℕ) : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (R ⧸ I ^ n)))
  /-- The transition `L_{n+1} ⟶ Res L_n`. -/
  map (n : ℕ) : obj (n + 1) ⟶ (levelTransitionRestrictScalars X I n.le_succ).obj (obj n)
  /-- The transition exhibits `L_n` as `L_{n+1} ⊗ᴸ_{A_{n+1}} A_n`. -/
  isDerivedBaseChange (n : ℕ) : Sheaf.IsDerivedBaseChange (map n)
  /-- Each level is bounded constructible of finite Tor amplitude. -/
  constructibleFiniteTor (n : ℕ) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (R ⧸ I ^ n)) X (obj n)

namespace AdicSystem

variable {I X} (S : AdicSystem I X)

/-- The tower `n ↦ Res L_n` in `D(X_proét, R)` of a normalized system, with the restricted
transitions. -/
noncomputable def restrict :
    ℕᵒᵖ ⥤ DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)) :=
  Functor.ofOpSequence (X := fun n ↦ (levelRestrictScalars X I n).obj (S.obj n)) fun n ↦
    (levelRestrictScalars X I (n + 1)).map (S.map n) ≫
      (levelRestrictScalarsCompIso X I n.le_succ).hom.app (S.obj n)

/-- The tower of a normalized system is normalized in the sense of
`AlgebraicGeometry.ProEtale.IsNormalizedTower`, so that its realization reduces to the levels
(`AlgebraicGeometry.ProEtale.exists_derivedCompletionDiagram_iso`). -/
lemma isNormalizedTower_restrict : IsNormalizedTower I S.restrict S.obj :=
  ⟨fun n ↦ Iso.refl _, S.map, S.isDerivedBaseChange, fun n ↦ by
    simp only [Iso.refl_hom, Iso.refl_inv, Category.id_comp]
    erw [Category.comp_id]
    exact Functor.ofOpSequence_map_homOfLE_succ (C := DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))) _ n⟩

/-- The quotient map `R ⟶ A_{n+1} = R ⧸ Iⁿ⁺¹`, indexing the levels from `1`. -/
noncomputable abbrev levelπ (I : Ideal R) (n : ℕ) : R →+* R ⧸ I ^ (n + 1) :=
  Ideal.Quotient.mk (I ^ (n + 1))

/-- The transition `A_{n+2} ⟶ A_{n+1}` between the levels indexed from `1`. -/
noncomputable abbrev levelρ (I : Ideal R) (n : ℕ) : R ⧸ I ^ (n + 1 + 1) →+* R ⧸ I ^ (n + 1) :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (n + 1).le_succ)

lemma levelπ_eq (I : Ideal R) (n : ℕ) : levelπ I n = (levelρ I n).comp (levelπ I (n + 1)) :=
  (Ideal.Quotient.factor_comp_mk _).symm

section Geometric

variable {k : Type u} [Field k] [IsSepClosed k] (aX : X ⟶ Spec (.of k)) [IsGeometric aX]
  [HasCompactification aX] [∀ n, Finite (R ⧸ I ^ n)]
  [∀ n, HasInvertibleExponent (R ⧸ I ^ n) (Spec (.of k))]

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
          ((levelTransitionRestrictScalars X I n.le_succ).obj (S.obj n)) ≅
          (ModuleCat.derivedRestrictScalars
            (Ideal.Quotient.factor (Ideal.pow_le_pow_right n.le_succ))).obj
            ((compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ n)) aX).obj
              (S.obj n)),
        ModuleCat.IsDerivedBaseChange
          ((compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))) aX).map
            (S.map n) ≫ e.hom)) ∧
      ∀ x : Spec (.of k) ⟶ X, x ≫ aX = 𝟙 _ →
        ((geometricStalk (R ⧸ I ^ n) x).obj (S.obj n)).IsPerfect ∧
        ∃ e : (geometricStalk (R ⧸ I ^ (n + 1)) x).obj
            ((levelTransitionRestrictScalars X I n.le_succ).obj (S.obj n)) ≅
            (ModuleCat.derivedRestrictScalars
              (Ideal.Quotient.factor (Ideal.pow_le_pow_right n.le_succ))).obj
              ((geometricStalk (R ⧸ I ^ n) x).obj (S.obj n)),
          ModuleCat.IsDerivedBaseChange
            ((geometricStalk (R ⧸ I ^ (n + 1)) x).map (S.map n) ≫ e.hom) := by
  have hsurj : Function.Surjective
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := I) n.le_succ)) :=
    Ideal.Quotient.factor_surjective _
  have hP := isPerfect_compactlySupportedGlobalSections_obj aX (S.constructibleFiniteTor n)
  refine ⟨hP.1, ?_, fun x hx ↦ ⟨hP.2 x hx, ?_⟩⟩
  · obtain ⟨α, hα⟩ := exists_isCoefficientChange_compactlySupportedGlobalSections _ aX hsurj
    exact ⟨α.app _, hα _ (S.constructibleFiniteTor (n + 1)) (S.isDerivedBaseChange n)⟩
  · obtain ⟨α, hα⟩ := exists_isCoefficientChange_stalk _ aX hsurj x hx
    exact ⟨α.app _, hα _ (S.constructibleFiniteTor (n + 1)) (S.isDerivedBaseChange n)⟩

/-- Blueprint `prop-trf-adic-coefficient-morphism-systems` (1): the normalized tower of perfect
complexes `P_n = RΓ_c(X, L_n)` over the local rings `A_n = R ⧸ Iⁿ`, `n ≥ 1`, with transitions
`RΓ_c(X, ν_n)` read through coefficient identifications `α n`
(`AlgebraicGeometry.ProEtale.exists_isCoefficientChange_compactlySupportedGlobalSections`). -/
noncomputable def compactSupportTower
    (α : ∀ n : ℕ, Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) (levelρ I n) ⋙
        compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1 + 1))) aX ≅
      compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))) aX ⋙
        ModuleCat.derivedRestrictScalars (levelρ I n))
    (hα : ∀ n : ℕ, IsCoefficientChange (levelρ I n) _ _ (α n)) :
    ModuleCat.NormalizedPerfectTower (levelπ I) (levelρ I) (levelπ_eq I) where
  obj n := (compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))) aX).obj
    (S.obj (n + 1))
  isPerfect n := (isPerfect_compactlySupportedGlobalSections_obj aX
    (S.constructibleFiniteTor (n + 1))).1
  map n := (compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1 + 1))) aX).map
    (S.map (n + 1)) ≫ (α n).hom.app (S.obj (n + 1))
  isDerivedBaseChange n :=
    hα n _ (S.constructibleFiniteTor (n + 1 + 1)) (S.isDerivedBaseChange (n + 1))

/-- Blueprint `prop-trf-adic-coefficient-morphism-systems` (1): the normalized tower of perfect
complexes `P_{x̄, n} = (L_n)_x̄` of geometric stalks at a geometric point `x̄`, `n ≥ 1`, with
transitions `(ν_n)_x̄` read through coefficient identifications `α n`
(`AlgebraicGeometry.ProEtale.exists_isCoefficientChange_stalk`). -/
noncomputable def stalkTower (x : Spec (.of k) ⟶ X) (hx : x ≫ aX = 𝟙 _)
    (α : ∀ n : ℕ, Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) (levelρ I n) ⋙
        geometricStalk (R ⧸ I ^ (n + 1 + 1)) x ≅
      geometricStalk (R ⧸ I ^ (n + 1)) x ⋙ ModuleCat.derivedRestrictScalars (levelρ I n))
    (hα : ∀ n : ℕ, IsCoefficientChange (levelρ I n) _ _ (α n)) :
    ModuleCat.NormalizedPerfectTower (levelπ I) (levelρ I) (levelπ_eq I) where
  obj n := (geometricStalk (R ⧸ I ^ (n + 1)) x).obj (S.obj (n + 1))
  isPerfect n := (isPerfect_compactlySupportedGlobalSections_obj aX
    (S.constructibleFiniteTor (n + 1))).2 x hx
  map n := (geometricStalk (R ⧸ I ^ (n + 1 + 1)) x).map (S.map (n + 1)) ≫
    (α n).hom.app (S.obj (n + 1))
  isDerivedBaseChange n :=
    hα n _ (S.constructibleFiniteTor (n + 1 + 1)) (S.isDerivedBaseChange (n + 1))

end Geometric

end AdicSystem

section Levels

variable {I} {ϖ : R} (hI : I = Ideal.span {ϖ})

/-- The quotients `R ⧸ Iⁿ⁺¹` of a local ring by the powers of an ideal `I` in its maximal ideal
are local. -/
lemma isLocalRing_quotient_pow [IsLocalRing R] (hle : I ≤ IsLocalRing.maximalIdeal R)
    (n : ℕ) : IsLocalRing (R ⧸ I ^ (n + 1)) :=
  have : Nontrivial (R ⧸ I ^ (n + 1)) := Ideal.Quotient.nontrivial fun h ↦
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top
      (top_le_iff.1 (h ▸ (Ideal.pow_le_self n.succ_ne_zero).trans hle))
  IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective

include hI in
lemma ker_levelπ (n : ℕ) : RingHom.ker (levelπ I n) = Ideal.span {ϖ ^ (n + 1)} := by
  rw [Ideal.mk_ker, hI, Ideal.span_singleton_pow]

lemma levelπ_surjective (n : ℕ) : Function.Surjective (levelπ I n) :=
  Ideal.Quotient.mk_surjective

lemma exists_levelπ_eq [IsPrecomplete I R] (x : ∀ n : ℕ, R ⧸ I ^ (n + 1))
    (hx : ∀ n, levelρ I n (x (n + 1)) = x n) : ∃ r : R, ∀ n, levelπ I n r = x n :=
  IsPrecomplete.exists_mk_eq_of_factor_eq x hx

lemma eq_zero_of_forall_levelπ_eq_zero [IsHausdorff I R] (r : R) (h : ∀ n, levelπ I n r = 0) :
    r = 0 :=
  IsHausdorff.eq_zero_of_forall_mk_eq_zero r h

end Levels

namespace AdicSystem

variable {I X} (S : AdicSystem I X) {k : Type u} [Field k] [IsSepClosed k]
  (aX : X ⟶ Spec (.of k)) [IsGeometric aX] [HasCompactification aX] [∀ n, Finite (R ⧸ I ^ n)]
  [∀ n, HasInvertibleExponent (R ⧸ I ^ n) (Spec (.of k))] [IsLocalRing R] [IsAdicComplete I R]
  {ϖ : R} (hϖ : ϖ ∈ IsLocalRing.maximalIdeal R) (hI : I = Ideal.span {ϖ})

include hϖ hI in
/-- Blueprint `sk-prop-trace-adic` (ii) and `prop-trf-adic-coefficient-morphism-systems` (2),
compact cohomology: the derived limit `P_𝒪 = R lim_n RΓ_c(X, L_n)` over `R` of the compact
cohomology of a normalized system is perfect, represented by a bounded complex of finite free
`R`-modules, and it reduces to the levels: each projection `P_𝒪 ⟶ Res RΓ_c(X, L_{n+1})` exhibits
`RΓ_c(X, L_{n+1})` as `P_𝒪 ⊗ᴸ_R A_{n+1}`. -/
theorem compactSupportTower_realization
    (α : ∀ n : ℕ, Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) (levelρ I n) ⋙
        compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1 + 1))) aX ≅
      compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))) aX ⋙
        ModuleCat.derivedRestrictScalars (levelρ I n))
    (hα : ∀ n : ℕ, IsCoefficientChange (levelρ I n) _ _ (α n))
    {c : Cone (S.compactSupportTower aX α hα).restrict} (hc : IsHomotopyLimit c) :
    (∃ (M : CochainComplex (ModuleCat.{u + 1} R) ℤ) (a b : ℤ), M.IsStrictlyGE a ∧
      M.IsStrictlyLE b ∧ (∀ i, Module.Free R (M.X i) ∧ Module.Finite R (M.X i)) ∧
      Nonempty (c.pt ≅ DerivedCategory.Q.obj M)) ∧
    ∀ n, ModuleCat.IsDerivedBaseChange (f := levelπ I n) (c.π.app (op n)) := by
  have hle : I ≤ IsLocalRing.maximalIdeal R := by
    rw [hI, Ideal.span_le, Set.singleton_subset_iff]
    exact hϖ
  have := isLocalRing_quotient_pow hle
  exact ⟨(S.compactSupportTower aX α hα).exists_iso_Q_obj_of_isHomotopyLimit levelπ_surjective
      (ker_levelπ hI) exists_levelπ_eq eq_zero_of_forall_levelπ_eq_zero hc,
    (S.compactSupportTower aX α hα).isDerivedBaseChange_π_app levelπ_surjective (ker_levelπ hI)
      exists_levelπ_eq eq_zero_of_forall_levelπ_eq_zero hc⟩

include hϖ hI in
/-- Blueprint `sk-prop-trace-adic` (ii) and `prop-trf-adic-coefficient-morphism-systems` (2),
geometric stalks: the derived limit `P_{x̄, 𝒪} = R lim_n (L_n)_x̄` over `R` of the geometric
stalks of a normalized system is perfect, represented by a bounded complex of finite free
`R`-modules, and each projection `P_{x̄, 𝒪} ⟶ Res (L_{n+1})_x̄` exhibits `(L_{n+1})_x̄` as
`P_{x̄, 𝒪} ⊗ᴸ_R A_{n+1}`. -/
theorem stalkTower_realization (x : Spec (.of k) ⟶ X) (hx : x ≫ aX = 𝟙 _)
    (α : ∀ n : ℕ, Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) (levelρ I n) ⋙
        geometricStalk (R ⧸ I ^ (n + 1 + 1)) x ≅
      geometricStalk (R ⧸ I ^ (n + 1)) x ⋙ ModuleCat.derivedRestrictScalars (levelρ I n))
    (hα : ∀ n : ℕ, IsCoefficientChange (levelρ I n) _ _ (α n))
    {c : Cone (S.stalkTower aX x hx α hα).restrict} (hc : IsHomotopyLimit c) :
    (∃ (M : CochainComplex (ModuleCat.{u + 1} R) ℤ) (a b : ℤ), M.IsStrictlyGE a ∧
      M.IsStrictlyLE b ∧ (∀ i, Module.Free R (M.X i) ∧ Module.Finite R (M.X i)) ∧
      Nonempty (c.pt ≅ DerivedCategory.Q.obj M)) ∧
    ∀ n, ModuleCat.IsDerivedBaseChange (f := levelπ I n) (c.π.app (op n)) := by
  have hle : I ≤ IsLocalRing.maximalIdeal R := by
    rw [hI, Ideal.span_le, Set.singleton_subset_iff]
    exact hϖ
  have := isLocalRing_quotient_pow hle
  exact ⟨(S.stalkTower aX x hx α hα).exists_iso_Q_obj_of_isHomotopyLimit levelπ_surjective
      (ker_levelπ hI) exists_levelπ_eq eq_zero_of_forall_levelπ_eq_zero hc,
    (S.stalkTower aX x hx α hα).isDerivedBaseChange_π_app levelπ_surjective (ker_levelπ hI)
      exists_levelπ_eq eq_zero_of_forall_levelπ_eq_zero hc⟩

end AdicSystem

end AdicSystem

end AlgebraicGeometry.ProEtale
