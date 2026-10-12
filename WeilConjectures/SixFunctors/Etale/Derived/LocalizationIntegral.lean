/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.Recollement
public import WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect
public import WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Localization
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative

/-!
# The closed-support triangle on `Dᵇc(-, 𝒪_E)`

Let `Λ` be a Noetherian domain, complete for a principal ideal `I = (ϖ)` with `Λ ⧸ I` finite of
exponent invertible on a field `k`: the integral stage `Λ = 𝒪_E`, `I = 𝔪_E` of the `ℓ`-adic
formalism. The category `Dᵇc(X, Λ)` is
`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleIntegral I X`: the objects of
`D(X_ét, Λ)` which are derived complete for `I` and whose reductions `K ⊗ᴸ Λ ⧸ Iⁿ⁺¹` are bounded
constructible of Tor amplitude in one common interval.

This file proves clauses (1)–(4) and (1')–(4') of blueprint `prop-sf-localization-all-stages`
at the integral stage, for a closed immersion `i : Z ⟶ X` and the complementary quasi-compact
open immersion `j : U ⟶ X` of schemes of finite type over `k`.

## Main statements

- `AlgebraicGeometry.Etale.DerivedCategory.isTriangulated_boundedConstructibleIntegral`:
  `Dᵇc(X, Λ)` is a triangulated subcategory of `D(X_ét, Λ)`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Pretriangulated Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

variable {Λ : Type (u + 1)} [CommRing Λ] {I : Ideal Λ} {ϖ : Λ}

/-! ### Tor amplitude and closure properties -/

section Triangulated

section TorAmplitude

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X : Scheme.{u}}

/-- Tor amplitude is closed under extensions, with the interval widened: if `T` is distinguished
and `T.obj₁`, `T.obj₃` have Tor amplitude in `[a, b]` and `[c, d]`, then `T.obj₂` has Tor
amplitude in `[min a c, max b d]`. -/
lemma DerivedCategory.torAmplitudeIn_obj₂
    {T : Triangle (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A))} (hT : T ∈ distTriang _)
    {a b c d : ℤ} (h₁ : DerivedCategory.torAmplitudeIn A X a b T.obj₁)
    (h₃ : DerivedCategory.torAmplitudeIn A X c d T.obj₃) :
    DerivedCategory.torAmplitudeIn A X (min a c) (max b d) T.obj₂ :=
  fun F ↦ by
    let G := (-⊗ᴸ-(X)[A]).flip.obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj F)
    let := _root_.DerivedCategory.commShiftTensorRight
      (K := (_root_.DerivedCategory.singleFunctor
        (Sheaf X.smallEtaleTopology A) 0).obj F)
    have : G.IsTriangulated := _root_.DerivedCategory.isTriangulated_tensorRight
      (K := (_root_.DerivedCategory.singleFunctor
        (Sheaf X.smallEtaleTopology A) 0).obj F)
    obtain ⟨g₁, l₁⟩ := (h₁ F).mono (min_le_left a c) (le_max_left b d)
    obtain ⟨g₃, l₃⟩ := (h₃ F).mono (min_le_right a c) (le_max_right b d)
    exact ⟨_root_.DerivedCategory.TStructure.t.isGE₂ _ (G.map_distinguished _ hT) _ g₁ g₃,
      _root_.DerivedCategory.TStructure.t.isLE₂ _ (G.map_distinguished _ hT) _ l₁ l₃⟩

end TorAmplitude

variable {X : Scheme.{u}}

/-- Derived completeness for `I = (ϖ)` is closed under isomorphisms. -/
lemma _root_.DerivedCategory.isClosedUnderIsomorphisms_derivedComplete
    (hϖ : ϖ ∈ nonZeroDivisors Λ) (hI : I = Ideal.span {ϖ}) :
    (_root_.DerivedCategory.derivedComplete X.smallEtaleTopology I).IsClosedUnderIsomorphisms := by
  rw [_root_.DerivedCategory.derivedComplete_eq_rightOrthogonal hϖ hI]
  infer_instance

/-- `Dᵇc(X, Λ)` is closed under isomorphisms. -/
lemma DerivedCategory.isClosedUnderIsomorphisms_boundedConstructibleIntegral
    (hϖ : ϖ ∈ nonZeroDivisors Λ) (hI : I = Ideal.span {ϖ}) :
    (DerivedCategory.boundedConstructibleIntegral I X).IsClosedUnderIsomorphisms where
  of_iso e := by
    have := _root_.DerivedCategory.isClosedUnderIsomorphisms_derivedComplete (X := X) hϖ hI
    rintro ⟨hc, a, b, h⟩
    exact ⟨(_root_.DerivedCategory.derivedComplete _ I).prop_of_iso e hc, a, b, fun n ↦
      ⟨(DerivedCategory.boundedConstructible _ X).prop_of_iso
          ((reductionModIdeal Λ X _).mapIso e) (h n).1,
        (DerivedCategory.torAmplitudeIn _ X a b).prop_of_iso
          ((reductionModIdeal Λ X _).mapIso e) (h n).2⟩⟩

end Triangulated

/-! ### Derived completeness through adjunctions

An object is derived complete for `I = (ϖ)` exactly when it receives no nonzero map from an
object on which `ϖ` acts invertibly (`DerivedCategory.derivedComplete_iff_rightOrthogonal`). A
right adjoint of a `Λ`-linear functor therefore preserves derived completeness. -/

section DerivedComplete

variable {X Y : Scheme.{u}} (hϖ : ϖ ∈ nonZeroDivisors Λ) (hI : I = Ideal.span {ϖ})
include hϖ hI

/-- A right adjoint `G` of a `Λ`-linear functor `F` between the derived categories of étale
sheaves of `Λ`-modules preserves derived completeness: a map `L ⟶ G K` from an object on which
`ϖ` acts invertibly corresponds to a map `F L ⟶ K`, and `ϖ` acts invertibly on `F L`. -/
lemma derivedComplete_obj_of_adjunction {F : 𝐃(Y, Λ) ⥤ 𝐃(X, Λ)} {G : 𝐃(X, Λ) ⥤ 𝐃(Y, Λ)}
    (adj : F ⊣ G) [F.Additive] [F.Linear Λ] {K : 𝐃(X, Λ)}
    (hK : _root_.DerivedCategory.derivedComplete X.smallEtaleTopology I K) :
    _root_.DerivedCategory.derivedComplete Y.smallEtaleTopology I (G.obj K) := by
  rw [_root_.DerivedCategory.derivedComplete_iff_rightOrthogonal hϖ hI] at hK ⊢
  intro L f (hL : IsIso (ϖ • 𝟙 L))
  have : IsIso (ϖ • 𝟙 (F.obj L)) := by
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_smul]
    infer_instance
  have h₀ : (adj.homEquiv L K).symm f = 0 := hK _ this
  have : G.Additive := adj.right_adjoint_additive
  rw [← (adj.homEquiv L K).apply_symm_apply f, h₀, adj.homEquiv_apply, Functor.map_zero,
    Limits.comp_zero]

/-- `Rf_*` preserves derived completeness, being right adjoint to the `Λ`-linear `Lf^*`. -/
lemma derivedComplete_rightDerivedLowerStar_obj (f : X ⟶ Y) {K : 𝐃(X, Λ)}
    (hK : _root_.DerivedCategory.derivedComplete X.smallEtaleTopology I K) :
    _root_.DerivedCategory.derivedComplete Y.smallEtaleTopology I
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) :=
  derivedComplete_obj_of_adjunction hϖ hI
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f) hK

/-- `Rf^!` preserves derived completeness, being right adjoint to the `Λ`-linear `Rf_!`. -/
lemma derivedComplete_rightDerivedUpperShriek_obj (f : X ⟶ Y) [HasCompactification f]
    [(R(f)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] {K : 𝐃(Y, Λ)}
    (hK : _root_.DerivedCategory.derivedComplete Y.smallEtaleTopology I K) :
    _root_.DerivedCategory.derivedComplete X.smallEtaleTopology I
      ((R(f)^![ModuleCat.{u + 1} Λ]).obj K) :=
  derivedComplete_obj_of_adjunction hϖ hI
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f) hK

/-- For an open immersion `j`, the pullback `Lj^*` preserves derived completeness, being right
adjoint to the `Λ`-linear extension by zero `D(j_!)`. -/
lemma derivedComplete_leftDerivedUpperStar_obj (j : X ⟶ Y) [IsOpenImmersion j] {K : 𝐃(Y, Λ)}
    (hK : _root_.DerivedCategory.derivedComplete Y.smallEtaleTopology I K) :
    _root_.DerivedCategory.derivedComplete X.smallEtaleTopology I
      ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K) :=
  derivedComplete_obj_of_adjunction hϖ hI
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j).symm) hK

end DerivedComplete

/-! ### The reductions of the operations -/

section Reductions

variable {X Y : Scheme.{u}} (hϖ : ϖ ∈ nonZeroDivisors Λ) (hI : I = Ideal.span {ϖ})
include hϖ hI

/-- The reductions of `Lf^* K` are the pullbacks of the reductions of `K`, so they are bounded
constructible with the same Tor amplitude as those of `K`. -/
lemma boundedConstructible_and_torAmplitudeIn_reductionModIdeal_leftDerivedUpperStar
    (f : X ⟶ Y) {K : 𝐃(Y, Λ)} {a b : ℤ} (n : ℕ)
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
        ((reductionModIdeal Λ Y (I ^ (n + 1))).obj K) ∧
      DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b
        ((reductionModIdeal Λ Y (I ^ (n + 1))).obj K)) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
        ((reductionModIdeal Λ X (I ^ (n + 1))).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ∧
      DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
        ((reductionModIdeal Λ X (I ^ (n + 1))).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) := by
  subst hI
  obtain ⟨e⟩ := nonempty_iso_map_reductionModIdeal (L((f)^*[ModuleCat.{u + 1} Λ])) hϖ (n + 1) K
  exact ⟨(DerivedCategory.boundedConstructible _ X).prop_of_iso e
      (boundedConstructible_leftDerivedUpperStar _ f hK.1),
    (DerivedCategory.torAmplitudeIn _ X a b).prop_of_iso e
      (torAmplitudeIn_leftDerivedUpperStar _ f a b hK.2)⟩

/-- Blueprint `prop-sf-localization-all-stages`, clause (3') at the integral stage `𝒪_E`, for
`j^*`: for an open immersion `j`, the pullback `Lj^*` carries `Dᵇc(Y, Λ)` into `Dᵇc(X, Λ)`, and
the reductions keep their Tor amplitude interval. -/
theorem boundedConstructibleIntegral_leftDerivedUpperStar (j : X ⟶ Y) [IsOpenImmersion j]
    {K : 𝐃(Y, Λ)} (hK : DerivedCategory.boundedConstructibleIntegral I Y K) :
    DerivedCategory.boundedConstructibleIntegral I X ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K) := by
  obtain ⟨hc, a, b, h⟩ := hK
  exact ⟨derivedComplete_leftDerivedUpperStar_obj hϖ hI j hc, a, b, fun n ↦
    boundedConstructible_and_torAmplitudeIn_reductionModIdeal_leftDerivedUpperStar hϖ hI j n
      (h n)⟩

variable [IsNoetherianRing Λ] {k : Type u} [Field k] [HasInvertibleExponent (Λ ⧸ I) (Spec (.of k))]
  (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
  [LocallyOfFiniteType aY] [QuasiCompact aY]

omit hϖ hI [IsNoetherianRing Λ] [LocallyOfFiniteType aY] [QuasiCompact aY] in
include aY in
/-- The reductions of the objects of `D(X_ét, Λ)` are killed by an integer invertible on `Y`. -/
lemma exists_nsmul_id_reductionModIdeal_eq_zero (n : ℕ) :
    ∃ N : ℕ, NeZero N ∧ IsUnit (N : Γ(Y, ⊤)) ∧ ∀ K : 𝐃(X, Λ),
      N • 𝟙 ((reductionModIdeal Λ X (I ^ (n + 1))).obj K) = 0 := by
  have : HasInvertibleExponent (Λ ⧸ I) Y := HasInvertibleExponent.of_hom aY
  obtain ⟨m, hm0, hmΛ, hmY⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ ⧸ I) (X := Y)
  have hmI : (m : Λ) ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact hmΛ
  refine ⟨m ^ (n + 1), ⟨pow_ne_zero _ hm0.ne'⟩, by rw [Nat.cast_pow]; exact hmY.pow _,
    fun K ↦ nsmul_id_reductionModIdeal (by rw [Nat.cast_pow]; exact Ideal.pow_mem_pow hmI _) K⟩

/-- Blueprint `prop-sf-localization-all-stages`, clauses (1) and (1') at the integral stage
`𝒪_E`: for a separated morphism `f : X ⟶ Y` of schemes of finite type over `k` with
`dim X ≤ d`, `Rf_*` carries `Dᵇc(X, Λ)` into `Dᵇc(Y, Λ)`, and if the reductions of `K` have Tor
amplitude in `[a, b]`, those of `Rf_* K` have Tor amplitude in `[a, b + 2d]`. The direct image
preserves derived completeness, commutes with the reductions, and the finite-level statements
are the finiteness theorem and the Tor amplitude bound for direct images
(`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar`,
`AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedLowerStar`). -/
theorem boundedConstructibleIntegral_rightDerivedLowerStar (f : X ⟶ Y) (hf : f ≫ aY = aX)
    [IsSeparated f] (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) {K : 𝐃(X, Λ)}
    (hK : DerivedCategory.boundedConstructibleIntegral I X K) :
    DerivedCategory.boundedConstructibleIntegral I Y ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) ∧
      ∀ a b : ℤ, (∀ n : ℕ, DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
          ((reductionModIdeal Λ X (I ^ (n + 1))).obj K)) →
        ∀ n : ℕ, DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a (b + 2 * (d : ℤ))
          ((reductionModIdeal Λ Y (I ^ (n + 1))).obj ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K)) := by
  obtain ⟨hc, a₀, b₀, h₀⟩ := hK
  have key : ∀ (n : ℕ) (a b : ℤ),
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
        ((reductionModIdeal Λ X (I ^ (n + 1))).obj K) →
      DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
        ((reductionModIdeal Λ X (I ^ (n + 1))).obj K) →
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
          ((reductionModIdeal Λ Y (I ^ (n + 1))).obj ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K)) ∧
        DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a (b + 2 * (d : ℤ))
          ((reductionModIdeal Λ Y (I ^ (n + 1))).obj ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K)) := by
    intro n a b hbc hta
    obtain ⟨N, _, hNY, hN⟩ := exists_nsmul_id_reductionModIdeal_eq_zero (I := I) (X := X) aY n
    have hN' := hN K
    subst hI
    obtain ⟨e⟩ := nonempty_iso_map_reductionModIdeal (R((f)_*[ModuleCat.{u + 1} Λ])) hϖ (n + 1) K
    exact ⟨(DerivedCategory.boundedConstructible _ Y).prop_of_iso e
        (boundedConstructible_rightDerivedLowerStar _ aX aY f hf N hN' hNY hbc),
      (DerivedCategory.torAmplitudeIn _ Y _ _).prop_of_iso e
        (torAmplitudeIn_rightDerivedLowerStar _ aX aY f hf d hd a b N hN' hNY hbc hta)⟩
  refine ⟨⟨derivedComplete_rightDerivedLowerStar_obj hϖ hI f hc, a₀, b₀ + 2 * (d : ℤ),
    fun n ↦ key n a₀ b₀ (h₀ n).1 (h₀ n).2⟩, fun a b hab n ↦ (key n a b (h₀ n).1 (hab n)).2⟩

end Reductions

end Etale

end AlgebraicGeometry
