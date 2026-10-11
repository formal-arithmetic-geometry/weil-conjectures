/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalCoefficient
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationMap
public import WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect
public import WeilConjectures.Mathlib.CategoryTheory.Idempotents.FunctorExtension
public import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.DerivedComplete
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantSheaf
public import WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.Derived.Stability

/-!
# The direct image along a closed immersion is fully faithful at every coefficient stage

Blueprint `prop-sf-closed-unit-all-stages`: for a closed immersion `i : Z ⟶ X`, the direct image
`i_* = Ri_* = Ri_!` is fully faithful on the categories `Dᵇc(-, Λ)` at each of the coefficient
stages `Λ = A_{E,n}, 𝒪_E, E, ℚ̄_ℓ`, and consequently, at every stage at which `i_*` has a right
adjoint `Ri^!` on these categories, the unit `Q ⟶ Ri^! i_* Q` is an isomorphism.

In this repository the stages are realised as follows, for schemes of finite type over an
algebraically closed field `k` (blueprint `sk-def-sf-setting`: `k = 𝔽̄_q`), the coefficients
being torsion of order invertible in `k`.

* `A_{E,n}`: `Dᵇc_proét(-, Λ)`, `Λ` finite
  (`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible`); the functor is
  `AlgebraicGeometry.ProEtale.boundedConstructibleLowerStar`. On the ambient categories the right
  adjoint exists (`prop-sf-closed-immersion-unit`).
* `𝒪_E`: `AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleIntegral`, the derived
  complete objects of `D(X_ét, 𝒪_E)` whose reductions modulo `𝔪_Eⁿ` are bounded constructible of
  uniformly bounded Tor amplitude; the functor is
  `AlgebraicGeometry.Etale.boundedConstructibleIntegralLowerStar`.
* `E`: the Karoubi envelope of the rationalization of `Dᵇc(-, 𝒪_E)`
  (`AlgebraicGeometry.Etale.DerivedCategoryBoundedConstructibleRational`, blueprint
  `def-weil-rationalization-karoubi`), the rationalization realised inside the rationalization
  `D_comp(X_ét, E)` of the derived complete objects; the functor is
  `AlgebraicGeometry.Etale.boundedConstructibleRationalLowerStar`.
* `ℚ̄_ℓ`: bounded complexes of sheaves of modules over the constant `ℓ`-adic sheaf with
  constructible cohomology (`AlgebraicGeometry.ProEtale.DerivedCategory.boundedAdicConstructible`),
  the Bhatt–Scholze model of the `2`-colimit of the `Dᵇc(-, E)`; the functor is
  `AlgebraicGeometry.ProEtale.boundedAdicConstructibleLowerStar`.

At each stage `Ri_*` sends `Dᵇc(Z, Λ)` into `Dᵇc(X, Λ)` by the finiteness theorems of the
repository, and the corestricted functor is fully faithful: `Ri_*` is fully faithful on the
whole ambient derived category (integral and `ℚ̄_ℓ` stages: because `i_*` is fully faithful and
preserves K-injective complexes), the functor induced on rationalizations by a fully faithful
linear triangulated functor is fully faithful (`CategoryTheory.Rationalization.full_map`, the
blueprint's argument that bijectivity persists after tensoring with `E`), and Karoubi extension
preserves full faithfulness (`CategoryTheory.Idempotents.full_functorExtension₂_obj`). The unit
of any right adjoint of a fully faithful functor is an isomorphism.

The blueprint's proof at the integral stage goes through the Roos triangles of the `𝒪_E`-adic
towers; in the derived-complete model used here this is unnecessary, `Ri_*` being fully faithful
on the whole derived category of `𝒪_E`-modules.
-/

@[expose] public section

universe w u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

section Finite

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- Blueprint `prop-sf-closed-unit-all-stages`, finite stage `A_{E,n}`: the direct image
`Ri_*` along a closed immersion is fully faithful on the bounded constructible pro-étale
complexes `Dᵇc_proét(Z, Λ)`, `Λ` finite. -/
instance ProEtale.full_boundedConstructible_ι_comp_rightDerivedLowerStar :
    ((ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z).ι ⋙
      (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) i).rightDerivedFunctor).Full :=
  inferInstance

instance ProEtale.faithful_boundedConstructible_ι_comp_rightDerivedLowerStar :
    ((ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z).ι ⋙
      (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) i).rightDerivedFunctor).Faithful :=
  inferInstance


end Finite

section Integral

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Small.{u + 1} E] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E]

/-- `Rf_*` on derived complete objects, as a functor between the full subcategories of
`AlgebraicGeometry.DerivedCategory.derivedCompleteIntegral`. -/
noncomputable abbrev Etale.rightDerivedLowerStarDerivedCompleteIntegralAux {Y X : Scheme.{u}}
    (f : Y ⟶ X) :
    (DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E).FullSubcategory ⥤
      (DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E).FullSubcategory :=
  (DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E).lift
    ((DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E).ι ⋙
      (Etale.lowerStar (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)))
        f).rightDerivedFunctor)
    (fun K ↦ Etale.derivedCompleteIntegral_rightDerivedLowerStar l E f _ K.property)

/-- The direct image `Rf_* : D_comp(Y_ét, 𝒪_E) ⥤ D_comp(X_ét, 𝒪_E)` on derived complete
objects, the restriction of `Rf_*`
(`AlgebraicGeometry.Etale.derivedCompleteIntegral_rightDerivedLowerStar`). -/
noncomputable def Etale.rightDerivedLowerStarDerivedCompleteIntegral {Y X : Scheme.{u}}
    (f : Y ⟶ X) :
    DerivedCategoryDerivedCompleteIntegral Y.smallEtaleTopology l E ⥤
      DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E :=
  Etale.rightDerivedLowerStarDerivedCompleteIntegralAux l E f

noncomputable instance {Y X : Scheme.{u}} (f : Y ⟶ X) :
    (Etale.rightDerivedLowerStarDerivedCompleteIntegral l E f).CommShift ℤ :=
  inferInstanceAs ((Etale.rightDerivedLowerStarDerivedCompleteIntegralAux l E f).CommShift ℤ)

instance {Y X : Scheme.{u}} (f : Y ⟶ X) :
    (Etale.rightDerivedLowerStarDerivedCompleteIntegral l E f).IsTriangulated :=
  inferInstanceAs
    (Etale.rightDerivedLowerStarDerivedCompleteIntegralAux l E f).IsTriangulated

instance {Y X : Scheme.{u}} (f : Y ⟶ X) :
    (Etale.rightDerivedLowerStarDerivedCompleteIntegral l E f).Linear
      (Shrink.{u + 1} (PadicAlgCl.integers l E)) where
  map_smul _ _ :=
    (DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E).ι.map_injective <|
      (Etale.lowerStar (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)))
        f).rightDerivedFunctor.map_smul _ _

/-- The right derived direct image along a closed immersion is fully faithful on étale sheaves
with values in any Grothendieck abelian category: `i_*` is fully faithful
(`AlgebraicGeometry.Etale.full_lowerStar_of_isClosedImmersion`) and preserves K-injective
complexes as a right adjoint of the exact `i^*`. -/
instance Etale.full_rightDerivedFunctor_lowerStar_of_isClosedImmersion (A : Type*)
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] :
    (Etale.lowerStar A i).rightDerivedFunctor.Full :=
  have : (Etale.lowerStar A i).PreservesKInjectiveComplexes :=
    (Etale.upperStarLowerStarAdjunction A i).preservesKInjectiveComplexes
  inferInstance

instance Etale.faithful_rightDerivedFunctor_lowerStar_of_isClosedImmersion (A : Type*)
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] :
    (Etale.lowerStar A i).rightDerivedFunctor.Faithful :=
  have : (Etale.lowerStar A i).PreservesKInjectiveComplexes :=
    (Etale.upperStarLowerStarAdjunction A i).preservesKInjectiveComplexes
  inferInstance

/-- Blueprint `prop-sf-closed-unit-all-stages`, integral stage `𝒪_E`: the direct image `Ri_*`
along a closed immersion is fully faithful on the derived complete objects
`D_comp(Z_ét, 𝒪_E)`. -/
instance Etale.full_rightDerivedLowerStarDerivedCompleteIntegral :
    (Etale.rightDerivedLowerStarDerivedCompleteIntegral l E i).Full :=
  inferInstanceAs (Etale.rightDerivedLowerStarDerivedCompleteIntegralAux l E i).Full

instance Etale.faithful_rightDerivedLowerStarDerivedCompleteIntegral :
    (Etale.rightDerivedLowerStarDerivedCompleteIntegral l E i).Faithful :=
  inferInstanceAs (Etale.rightDerivedLowerStarDerivedCompleteIntegralAux l E i).Faithful

/-- The direct image `Rf_* : D_comp(Y_ét, E) ⥤ D_comp(X_ét, E)` at the rational stage, induced
on the rationalizations by `AlgebraicGeometry.Etale.rightDerivedLowerStarDerivedCompleteIntegral`.
-/
noncomputable def Etale.rightDerivedLowerStarDerivedCompleteRational {Y X : Scheme.{u}}
    (f : Y ⟶ X) :
    DerivedCategoryDerivedCompleteRational Y.smallEtaleTopology l E ⥤
      DerivedCategoryDerivedCompleteRational X.smallEtaleTopology l E :=
  Rationalization.map _ (Etale.rightDerivedLowerStarDerivedCompleteIntegral l E f)

/-- Blueprint `prop-sf-closed-unit-all-stages`, rational stage `E`: the direct image `Ri_*`
along a closed immersion is fully faithful on `D_comp(Z_ét, E)`. -/
instance Etale.full_rightDerivedLowerStarDerivedCompleteRational :
    (Etale.rightDerivedLowerStarDerivedCompleteRational l E i).Full :=
  Rationalization.full_map _

instance Etale.faithful_rightDerivedLowerStarDerivedCompleteRational :
    (Etale.rightDerivedLowerStarDerivedCompleteRational l E i).Faithful :=
  Rationalization.faithful_map _

/-- Blueprint `prop-sf-closed-unit-all-stages`, the unit at the integral stage: for any right
adjoint `Ri^!` of `Ri_* : D_comp(Z_ét, 𝒪_E) ⥤ D_comp(X_ét, 𝒪_E)`, the unit `Q ⟶ Ri^! Ri_* Q` is an
isomorphism. -/
theorem Etale.isIso_unit_app_rightDerivedLowerStarDerivedCompleteIntegral
    {G : DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E ⥤
      DerivedCategoryDerivedCompleteIntegral Z.smallEtaleTopology l E}
    (adj : Etale.rightDerivedLowerStarDerivedCompleteIntegral l E i ⊣ G)
    (Q : DerivedCategoryDerivedCompleteIntegral Z.smallEtaleTopology l E) :
    IsIso (adj.unit.app Q) :=
  inferInstance

/-- Blueprint `prop-sf-closed-unit-all-stages`, the unit at the rational stage: for any right
adjoint `Ri^!` of `Ri_* : D_comp(Z_ét, E) ⥤ D_comp(X_ét, E)`, the unit `Q ⟶ Ri^! Ri_* Q` is an
isomorphism. -/
theorem Etale.isIso_unit_app_rightDerivedLowerStarDerivedCompleteRational
    {G : DerivedCategoryDerivedCompleteRational X.smallEtaleTopology l E ⥤
      DerivedCategoryDerivedCompleteRational Z.smallEtaleTopology l E}
    (adj : Etale.rightDerivedLowerStarDerivedCompleteRational l E i ⊣ G)
    (Q : DerivedCategoryDerivedCompleteRational Z.smallEtaleTopology l E) :
    IsIso (adj.unit.app Q) :=
  inferInstance

end Integral

section BoundedConstructible

/-! ### `i_* : Dᵇc(Z, Λ) ⥤ Dᵇc(X, Λ)` at every stage

Following blueprint `sk-def-sf-setting`, the schemes are of finite type over an algebraically
closed field `k` (there `k = 𝔽̄_q`), and the coefficients are torsion of order invertible in `k`.
At each stage, `Ri_*` sends `Dᵇc(Z, Λ)` into `Dᵇc(X, Λ)` by the finiteness theorems of
`sk-prop-sf-finiteness` and `sk-cor-sf-direct-image-ctf`; the corestricted functor is fully
faithful, so the unit of any right adjoint is an isomorphism. -/

variable {k : Type u} [Field k] (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
  [QuasiCompact aX]

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

section Finite

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] (N : ℕ) (hN : (N : k) ≠ 0)
  (hNΛ : (N : Λ) = 0)

include aX hN hNΛ in
/-- `Ri_*` sends `Dᵇc_proét(Z, Λ)` into `Dᵇc_proét(X, Λ)` for a finite `Λ` of exponent `N`
invertible in `k` (`AlgebraicGeometry.ProEtale.boundedConstructible_rightDerivedLowerStar`). -/
lemma ProEtale.boundedConstructible_rightDerivedLowerStar_of_isClosedImmersion
    {K : DerivedCategory (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} Λ))}
    (hK : ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z K) :
    ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
      ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) i).rightDerivedFunctor.obj K) :=
  ProEtale.boundedConstructible_rightDerivedLowerStar (ModuleCat.{u + 1} Λ) N hN
    (fun M ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦ by
      simp [← Nat.cast_smul_eq_nsmul Λ, hNΛ])) aX i hK

/-- Blueprint `prop-sf-closed-unit-all-stages`, finite stage `A_{E,n}`: the direct image
`i_* : Dᵇc_proét(Z, Λ) ⥤ Dᵇc_proét(X, Λ)`. -/
noncomputable def ProEtale.boundedConstructibleLowerStar :
    (ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z).FullSubcategory ⥤
      (ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X).FullSubcategory :=
  (ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X).lift
    ((ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z).ι ⋙
      (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) i).rightDerivedFunctor)
    (fun K ↦ ProEtale.boundedConstructible_rightDerivedLowerStar_of_isClosedImmersion i aX N hN
      hNΛ K.property)

/-- Blueprint `prop-sf-closed-unit-all-stages`, finite stage: `i_*` is fully faithful on
`Dᵇc_proét(-, Λ)`. -/
instance ProEtale.full_boundedConstructibleLowerStar :
    (ProEtale.boundedConstructibleLowerStar i aX N hN hNΛ).Full := by
  unfold ProEtale.boundedConstructibleLowerStar
  infer_instance

instance ProEtale.faithful_boundedConstructibleLowerStar :
    (ProEtale.boundedConstructibleLowerStar i aX N hN hNΛ).Faithful := by
  unfold ProEtale.boundedConstructibleLowerStar
  infer_instance

/-- Blueprint `prop-sf-closed-unit-all-stages`, the unit at the finite stage: for any right
adjoint `Ri^!` of `i_* : Dᵇc_proét(Z, Λ) ⥤ Dᵇc_proét(X, Λ)`, the unit `Q ⟶ Ri^! i_* Q` is an
isomorphism. On the ambient categories the right adjoint exists and this is
`AlgebraicGeometry.ProEtale.isIso_derivedLowerStarClosedUpperShriekAdjunction_unit_app`. -/
theorem ProEtale.isIso_unit_app_boundedConstructibleLowerStar
    {G : (ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X).FullSubcategory ⥤
      (ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z).FullSubcategory}
    (adj : ProEtale.boundedConstructibleLowerStar i aX N hN hNΛ ⊣ G)
    (Q : (ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z).FullSubcategory) :
    IsIso (adj.unit.app Q) :=
  inferInstance

end Finite

section Integral

variable {Λ : Type (u + 1)} [CommRing Λ] [IsDomain Λ] [IsNoetherianRing Λ] (I : Ideal Λ)
  (hI : I.IsPrincipal) [HasInvertibleExponent (Λ ⧸ I) X]

namespace Etale

include aX hI in
/-- `Ri_*` sends `Dᵇc(Z, Λ)` into `Dᵇc(X, Λ)` at the integral stage
(`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleIntegral`): `Ri_*` preserves derived
completeness (`AlgebraicGeometry.Etale.derivedComplete_rightDerivedLowerStar`), commutes with the
reductions modulo `Iⁿ⁺¹`
(`AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerStar`),
and preserves bounded constructibility and Tor amplitude intervals of torsion complexes
(`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar`,
`AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedLowerStar`). -/
lemma boundedConstructibleIntegral_rightDerivedLowerStar_of_isClosedImmersion
    {K : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructibleIntegral I Z K) :
    DerivedCategory.boundedConstructibleIntegral I X
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) i).rightDerivedFunctor.obj K) := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le (i ≫ aX)
  obtain ⟨hc, a, b, hab⟩ := hK
  refine ⟨derivedComplete_rightDerivedLowerStar I hI i K hc, a, b + 2 * (d : ℤ), fun n ↦ ?_⟩
  obtain ⟨x, hx⟩ := hI.principal
  have hJ : (I ^ (n + 1)).IsPrincipal :=
    ⟨⟨x ^ (n + 1), by rw [hx, Ideal.submodule_span_eq, Ideal.span_singleton_pow]⟩⟩
  obtain ⟨e⟩ := nonempty_iso_reductionModIdeal_rightDerivedLowerStar Λ i _ hJ
  obtain ⟨hbc, hta⟩ := hab n
  -- the reduction is killed by `N = mⁿ⁺¹`, for `m` the exponent of `Λ/I`
  obtain ⟨m, hm0, hmΛ, hmY⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ ⧸ I)
    (X := X)
  have hmI : (m : Λ) ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact hmΛ
  have : NeZero (m ^ (n + 1)) := ⟨pow_ne_zero _ hm0.ne'⟩
  have hNY : IsUnit ((m ^ (n + 1) : ℕ) : Γ(X, ⊤)) := by
    rw [Nat.cast_pow]; exact hmY.pow _
  have hN := nsmul_id_reductionModIdeal (J := I ^ (n + 1)) (N := m ^ (n + 1))
    (by rw [Nat.cast_pow]; exact Ideal.pow_mem_pow hmI _) K
  exact ⟨(DerivedCategory.boundedConstructible _ _).prop_of_iso (e.app K).symm
      (boundedConstructible_rightDerivedLowerStar _ (i ≫ aX) aX i rfl _ hN hNY hbc),
    (DerivedCategory.torAmplitudeIn _ _ _ _).prop_of_iso (e.app K).symm
      (torAmplitudeIn_rightDerivedLowerStar _ (i ≫ aX) aX i rfl d hd a b _ hN hNY hbc hta)⟩

/-- Blueprint `prop-sf-closed-unit-all-stages`, integral stage: the direct image
`i_* : Dᵇc(Z, Λ) ⥤ Dᵇc(X, Λ)` on
`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleIntegral`
(for `Λ = 𝒪_E`, `I = 𝔪_E`). -/
noncomputable def boundedConstructibleIntegralLowerStar :
    (DerivedCategory.boundedConstructibleIntegral I Z).FullSubcategory ⥤
      (DerivedCategory.boundedConstructibleIntegral I X).FullSubcategory :=
  (DerivedCategory.boundedConstructibleIntegral I X).lift
    ((DerivedCategory.boundedConstructibleIntegral I Z).ι ⋙
      (Etale.lowerStar (ModuleCat.{u + 1} Λ) i).rightDerivedFunctor)
    (fun K ↦ boundedConstructibleIntegral_rightDerivedLowerStar_of_isClosedImmersion i aX I hI
      K.property)

/-- Blueprint `prop-sf-closed-unit-all-stages`, integral stage: `i_*` is fully faithful on
`Dᵇc(-, 𝒪_E)`, `Ri_*` being fully faithful on the whole étale derived category. -/
instance full_boundedConstructibleIntegralLowerStar :
    (boundedConstructibleIntegralLowerStar i aX I hI).Full := by
  unfold boundedConstructibleIntegralLowerStar
  infer_instance

instance faithful_boundedConstructibleIntegralLowerStar :
    (boundedConstructibleIntegralLowerStar i aX I hI).Faithful := by
  unfold boundedConstructibleIntegralLowerStar
  infer_instance

/-- Blueprint `prop-sf-closed-unit-all-stages`, the unit at the integral stage: for any right
adjoint `Ri^!` of `i_* : Dᵇc(Z, 𝒪_E) ⥤ Dᵇc(X, 𝒪_E)`, the unit `Q ⟶ Ri^! i_* Q` is an
isomorphism. -/
theorem isIso_unit_app_boundedConstructibleIntegralLowerStar
    {G : (DerivedCategory.boundedConstructibleIntegral I X).FullSubcategory ⥤
      (DerivedCategory.boundedConstructibleIntegral I Z).FullSubcategory}
    (adj : boundedConstructibleIntegralLowerStar i aX I hI ⊣ G)
    (Q : (DerivedCategory.boundedConstructibleIntegral I Z).FullSubcategory) :
    IsIso (adj.unit.app Q) :=
  inferInstance

end Etale

end Integral

section Rational

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Small.{u + 1} E] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E]

/-- The objects of `D_comp(X_ét, E)` coming from `Dᵇc(X, 𝒪_E)`: the rationalization of
`Dᵇc(X, 𝒪_E)`, realised as a full subcategory of `D_comp(X_ét, E)`. Its `Hom` groups are those of
`Dᵇc(X, 𝒪_E)` with the nonzero elements of `𝒪_E` inverted
(`CategoryTheory.Rationalization.exists_smul_eq_map`,
`CategoryTheory.Rationalization.map_eq_map_iff`). -/
def Etale.DerivedCategory.boundedConstructibleRational (X : Scheme.{u}) :
    ObjectProperty (DerivedCategoryDerivedCompleteRational X.smallEtaleTopology l E) :=
  fun K ↦ ∃ L : DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E,
    Etale.DerivedCategory.boundedConstructibleIntegral (PadicAlgCl.maximalIdealShrink l E) X
      ((DerivedCategoryDerivedCompleteIntegral.ι _ l E).obj L) ∧
    Nonempty ((DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj L ≅ K)

/-- The rational stage `Dᵇc(X, E)` of blueprint `def-weil-rationalization-karoubi`: the Karoubi
envelope of the rationalization of `Dᵇc(X, 𝒪_E)`. -/
abbrev Etale.DerivedCategoryBoundedConstructibleRational (X : Scheme.{u}) :=
  Idempotents.Karoubi (Etale.DerivedCategory.boundedConstructibleRational l E X).FullSubcategory

/-- The ring of integers `𝒪_E` of a finite extension of `ℚ_ℓ` is noetherian, being a principal
ideal ring; so is its copy in `Type (u + 1)`. -/
instance : IsNoetherianRing (Shrink.{u + 1} (PadicAlgCl.integers l E)) :=
  isNoetherianRing_of_ringEquiv _ (Shrink.ringEquiv _).symm

variable [HasInvertibleExponent (Shrink.{u + 1} (PadicAlgCl.integers l E) ⧸
    PadicAlgCl.maximalIdealShrink l E) X]

include aX in
/-- `Ri_*` on `D_comp(-, E)` sends the rationalization of `Dᵇc(Z, 𝒪_E)` into that of
`Dᵇc(X, 𝒪_E)`: it carries `Q L` to `Q (Ri_* L)`, and `Ri_* L ∈ Dᵇc(X, 𝒪_E)`
(`Etale.boundedConstructibleIntegral_rightDerivedLowerStar_of_isClosedImmersion`). -/
lemma Etale.boundedConstructibleRational_rightDerivedLowerStar_of_isClosedImmersion
    {K : DerivedCategoryDerivedCompleteRational Z.smallEtaleTopology l E}
    (hK : Etale.DerivedCategory.boundedConstructibleRational l E Z K) :
    Etale.DerivedCategory.boundedConstructibleRational l E X
      ((Etale.rightDerivedLowerStarDerivedCompleteRational l E i).obj K) := by
  obtain ⟨L, hL, ⟨e⟩⟩ := hK
  refine ⟨(Etale.rightDerivedLowerStarDerivedCompleteIntegral l E i).obj L,
    Etale.boundedConstructibleIntegral_rightDerivedLowerStar_of_isClosedImmersion i aX _
      (PadicAlgCl.isPrincipal_maximalIdealShrink l E) hL,
    ⟨((Rationalization.mapFac _ (Etale.rightDerivedLowerStarDerivedCompleteIntegral l E i)).app
      L).symm ≪≫ (Etale.rightDerivedLowerStarDerivedCompleteRational l E i).mapIso e⟩⟩

/-- Blueprint `prop-sf-closed-unit-all-stages`, rational stage: the direct image
`i_* : Dᵇc(Z, E) ⥤ Dᵇc(X, E)`, the Karoubi extension of the functor induced on the
rationalizations of `Dᵇc(-, 𝒪_E)` by the integral `Ri_*`. -/
noncomputable def Etale.boundedConstructibleRationalLowerStar :
    Etale.DerivedCategoryBoundedConstructibleRational l E Z ⥤
      Etale.DerivedCategoryBoundedConstructibleRational l E X :=
  (Idempotents.functorExtension₂ _ _).obj
    ((Etale.DerivedCategory.boundedConstructibleRational l E X).lift
      ((Etale.DerivedCategory.boundedConstructibleRational l E Z).ι ⋙
        Etale.rightDerivedLowerStarDerivedCompleteRational l E i)
      (fun K ↦ Etale.boundedConstructibleRational_rightDerivedLowerStar_of_isClosedImmersion i aX
        l E K.property))

/-- Blueprint `prop-sf-closed-unit-all-stages`, rational stage: `i_*` is fully faithful on
`Dᵇc(-, E)`. The functor induced on rationalizations by the fully faithful integral `Ri_*` is
fully faithful (`CategoryTheory.Rationalization.full_map`), which is the blueprint's argument
that bijectivity persists after tensoring with `E`, and Karoubi extension preserves full
faithfulness (`CategoryTheory.Idempotents.full_functorExtension₂_obj`). -/
instance Etale.full_boundedConstructibleRationalLowerStar :
    (Etale.boundedConstructibleRationalLowerStar i aX l E).Full := by
  unfold Etale.boundedConstructibleRationalLowerStar
  infer_instance

instance Etale.faithful_boundedConstructibleRationalLowerStar :
    (Etale.boundedConstructibleRationalLowerStar i aX l E).Faithful := by
  unfold Etale.boundedConstructibleRationalLowerStar
  infer_instance

/-- Blueprint `prop-sf-closed-unit-all-stages`, the unit at the rational stage: for any right
adjoint `Ri^!` of `i_* : Dᵇc(Z, E) ⥤ Dᵇc(X, E)`, the unit `Q ⟶ Ri^! i_* Q` is an isomorphism. -/
theorem Etale.isIso_unit_app_boundedConstructibleRationalLowerStar
    {G : Etale.DerivedCategoryBoundedConstructibleRational l E X ⥤
      Etale.DerivedCategoryBoundedConstructibleRational l E Z}
    (adj : Etale.boundedConstructibleRationalLowerStar i aX l E ⊣ G)
    (Q : Etale.DerivedCategoryBoundedConstructibleRational l E Z) :
    IsIso (adj.unit.app Q) :=
  inferInstance

end Rational

section Adic

variable [IsAlgClosed k] (l : ℕ) [Fact l.Prime] (hl : ringChar k ≠ l)

/-- The counit `i^* i_* ⟶ 𝟭` on sheaves of modules over the constant `ℓ`-adic sheaf is an
isomorphism for a closed immersion `i`: its underlying map of sheaves of `ℚ̄_ℓ`-modules is the
counit of `ProEtale.upperStarLowerStarAdjunction`
(`AlgebraicGeometry.ProEtale.isIso_upperStarLowerStarAdjunction_counit`). -/
instance ProEtale.isIso_adicUpperStarLowerStarAdjunction_counit :
    IsIso (ProEtale.adicUpperStarLowerStarAdjunction l i).counit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro N
  have : IsIso ((ProEtale.adicUpperStarLowerStarAdjunction l i).counit.app N).hom := by
    rw [ProEtale.adicUpperStarLowerStarAdjunction, Adjunction.modAdjunction_counit_app_hom]
    infer_instance
  have : IsIso ((ProEtale.AdicSheaf.forget Z).map
      ((ProEtale.adicUpperStarLowerStarAdjunction l i).counit.app N)) := this
  exact isIso_of_reflects_iso _ (ProEtale.AdicSheaf.forget Z)

instance ProEtale.full_adicLowerStar : (ProEtale.adicLowerStar l i).Full :=
  (ProEtale.adicUpperStarLowerStarAdjunction l i).fullyFaithfulROfIsIsoCounit.full

instance ProEtale.faithful_adicLowerStar : (ProEtale.adicLowerStar l i).Faithful :=
  (ProEtale.adicUpperStarLowerStarAdjunction l i).fullyFaithfulROfIsIsoCounit.faithful

include aX hl in
/-- `Ri_*` sends `Dᵇc(Z, ℚ̄_ℓ)` into `Dᵇc(X, ℚ̄_ℓ)`
(`AlgebraicGeometry.ProEtale.DerivedCategory.boundedAdicConstructible`), by the finiteness
theorem `AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor` and dévissage. -/
lemma ProEtale.boundedAdicConstructible_rightDerivedLowerStar_of_isClosedImmersion
    {K : DerivedCategory (ProEtale.AdicSheaf l Z)}
    (hK : ProEtale.DerivedCategory.boundedAdicConstructible l Z K) :
    ProEtale.DerivedCategory.boundedAdicConstructible l X
      ((ProEtale.adicLowerStar l i).rightDerivedFunctor.obj K) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  exact ProEtale.finiteLowerStar_of_bounded i
    (fun F hF ↦ ProEtale.finiteLowerStar_singleFunctor aX i hl hF) K hK.1 hK.2

/-- Blueprint `prop-sf-closed-unit-all-stages`, stage `ℚ̄_ℓ`: the direct image
`i_* : Dᵇc(Z, ℚ̄_ℓ) ⥤ Dᵇc(X, ℚ̄_ℓ)` on bounded complexes of sheaves of modules over the constant
`ℓ`-adic sheaf with constructible cohomology, the Bhatt–Scholze model of the `2`-colimit of the
`Dᵇc(-, E)` (blueprint `def-weil-algebraically-closed-coefficients`). -/
noncomputable def ProEtale.boundedAdicConstructibleLowerStar :
    (ProEtale.DerivedCategory.boundedAdicConstructible l Z).FullSubcategory ⥤
      (ProEtale.DerivedCategory.boundedAdicConstructible l X).FullSubcategory :=
  (ProEtale.DerivedCategory.boundedAdicConstructible l X).lift
    ((ProEtale.DerivedCategory.boundedAdicConstructible l Z).ι ⋙
      (ProEtale.adicLowerStar l i).rightDerivedFunctor)
    (fun K ↦ ProEtale.boundedAdicConstructible_rightDerivedLowerStar_of_isClosedImmersion i aX l
      hl K.property)

/-- Blueprint `prop-sf-closed-unit-all-stages`, stage `ℚ̄_ℓ`: `i_*` is fully faithful on
`Dᵇc(-, ℚ̄_ℓ)`. The `ℓ`-adic `i_*` is fully faithful, its counit being an isomorphism, and
preserves K-injective complexes, so its right derived functor is fully faithful. -/
instance ProEtale.full_boundedAdicConstructibleLowerStar :
    (ProEtale.boundedAdicConstructibleLowerStar i aX l hl).Full := by
  unfold ProEtale.boundedAdicConstructibleLowerStar
  infer_instance

instance ProEtale.faithful_boundedAdicConstructibleLowerStar :
    (ProEtale.boundedAdicConstructibleLowerStar i aX l hl).Faithful := by
  unfold ProEtale.boundedAdicConstructibleLowerStar
  infer_instance

/-- Blueprint `prop-sf-closed-unit-all-stages`, the unit at the stage `ℚ̄_ℓ`: for any right
adjoint `Ri^!` of `i_* : Dᵇc(Z, ℚ̄_ℓ) ⥤ Dᵇc(X, ℚ̄_ℓ)`, the unit `Q ⟶ Ri^! i_* Q` is an
isomorphism. -/
theorem ProEtale.isIso_unit_app_boundedAdicConstructibleLowerStar
    {G : (ProEtale.DerivedCategory.boundedAdicConstructible l X).FullSubcategory ⥤
      (ProEtale.DerivedCategory.boundedAdicConstructible l Z).FullSubcategory}
    (adj : ProEtale.boundedAdicConstructibleLowerStar i aX l hl ⊣ G)
    (Q : (ProEtale.DerivedCategory.boundedAdicConstructible l Z).FullSubcategory) :
    IsIso (adj.unit.app Q) :=
  inferInstance

end Adic

end BoundedConstructible

end AlgebraicGeometry
