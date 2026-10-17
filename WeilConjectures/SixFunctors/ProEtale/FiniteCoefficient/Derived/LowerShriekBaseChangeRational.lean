/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.CompletionTriangulated
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalCoefficient
public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationRecollement
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChangeComplete
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Shift

/-!
# Compact-support base change over a finite extension of `ℚ_ℓ`

Let `E` be a finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ` with ring of integers `𝒪_E`. The integral stage
`D_comp(X_proét, 𝒪_E)` consists of the derived complete objects of `D(X_proét, 𝒪_E)`
(`DerivedCategoryDerivedCompleteIntegral`), and the rational stage `D_comp(X_proét, E)` is its
rationalization (`DerivedCategoryDerivedCompleteRational`), the category of
`def-weil-pbc-rational-category`. Following the blueprint, the operations of the rational stage
are obtained by transport from the integral stage (`prop-weil-pbc-rational-transport`,
`CategoryTheory.Rationalization.map`): the integral operations, `K ↦ (F K)^` for the plain
operation `F`, are `𝒪_E`-linear triangulated functors between the integral stages.

* `AlgebraicGeometry.ProEtale.integralRightDerivedLowerShriek`: the integral compact-support
  direct image `K ↦ (Rf_! K)^`, and `rationalRightDerivedLowerShriek` its transport to the rational
  stages (`def-weil-integral-rational-qbar-compact-support`).
* `AlgebraicGeometry.ProEtale.rationalRightDerivedLowerShriekOfCompactificationBaseChangeMap`:
  the rational compact-support exchange map, the transport of the completed one.

## Main statements

- `isIso_rationalRightDerivedLowerShriekOfCompactificationBaseChangeMap_app`
  (`thm-cbc-finite-extension`).
- `AlgebraicGeometry.ProEtale.nonempty_iso_fromIntegral_integralRightDerivedLowerShriek`
  (`lem-weil-compact-support-representative-independence`).
-/

@[expose] public section

universe w u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]
  [Small.{u + 1} E]

set_option hygiene false in
/-- The ring of integers `𝒪_E`, in the universe `u + 1`. -/
local notation "𝐎" => Shrink.{u + 1} (PadicAlgCl.integers l E)

set_option hygiene false in
/-- The derived category `D(X_proét, 𝒪_E)`. -/
local notation "𝐃(" X ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} 𝐎))

set_option hygiene false in
/-- The integral stage `D_comp(X_proét, 𝒪_E)`. -/
local notation "𝐃𝐜(" X ")" =>
  DerivedCategoryDerivedCompleteIntegral (Scheme.ProEt.topology X) l E

set_option hygiene false in
/-- The rational stage `D_comp(X_proét, E)`. -/
local notation "𝐃𝐐(" X ")" =>
  DerivedCategoryDerivedCompleteRational (Scheme.ProEt.topology X) l E

set_option hygiene false in
/-- The submonoid of nonzero elements of `𝒪_E`, inverted by the rationalization. -/
local notation "𝐌" => nonZeroDivisors 𝐎

/-! ### Integral operations -/

section Integral

variable {X Y : Scheme.{u}}

/-- The extension by zero along an open immersion, on the derived categories of pro-étale
sheaves of `Λ`-modules, is `Λ`-linear, being left adjoint to the `Λ`-linear restriction. -/
instance linear_mapDerivedCategory_openImmersionLowerShriek (Λ : Type (u + 1)) [CommRing Λ]
    {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    D((j)_!open[ModuleCat.{u + 1} Λ]).Linear Λ :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).left_adjoint_linear

/-- The compact-support direct image `Rf_!(c) = D(i_!) ⋙ R(g_*)` of pro-étale sheaves of
`Λ`-modules is `Λ`-linear. -/
instance linear_rightDerivedLowerShriekOfCompactification (Λ : Type (u + 1)) [CommRing Λ]
    {f : X ⟶ Y} (c : Compactification f) : Rf_!(c)[ModuleCat.{u + 1} Λ].Linear Λ :=
  inferInstanceAs ((D((c.i)_!open[ModuleCat.{u + 1} Λ]) ⋙
    R((c.g)_*[ModuleCat.{u + 1} Λ])).Linear Λ)

/-- The integral version `K ↦ (F K)^` of an operation `F : D(X_proét, 𝒪_E) ⥤ D(Y_proét, 𝒪_E)`,
a functor between the integral stages: the inclusion of the derived complete objects, followed by
`F` and by the derived completion. -/
noncomputable abbrev integralOperation (F : 𝐃(X) ⥤ 𝐃(Y)) : 𝐃𝐜(X) ⥤ 𝐃𝐜(Y) :=
  DerivedCategoryDerivedCompleteIntegral.ι _ l E ⋙ F ⋙
    DerivedCategoryDerivedCompleteIntegral.completion _ l E

/-- The integral compact-support direct image `K ↦ (Rf_!(c) K)^ = R lim_n Rf_!(c) K_n` of a
compactification `c` of `f` (blueprint `def-weil-integral-rational-qbar-compact-support`, at the
integral stage). -/
noncomputable abbrev integralRightDerivedLowerShriek {f : X ⟶ Y} (c : Compactification f) :
    𝐃𝐜(X) ⥤ 𝐃𝐜(Y) :=
  integralOperation l E Rf_!(c)[ModuleCat.{u + 1} 𝐎]

/-- Blueprint `def-weil-integral-rational-qbar-compact-support`, at the rational stage `E`: the
compact-support direct image `D_comp(X_proét, E) ⥤ D_comp(Y_proét, E)` of a compactification `c`
of `f`, the transport to the rationalizations of the integral compact-support direct image
(`CategoryTheory.Rationalization.map`). -/
noncomputable abbrev rationalRightDerivedLowerShriek {f : X ⟶ Y} (c : Compactification f) :
    𝐃𝐐(X) ⥤ 𝐃𝐐(Y) :=
  Rationalization.map 𝐌 (integralRightDerivedLowerShriek l E c)

/-- Blueprint `lem-weil-compact-support-representative-independence`: Independence of the integral
representative.

Let `K, K' ∈ D_comp(X_proét, 𝒪_E)` be integral complexes representing the same object of the
rationalized category `D_comp(X_proét, E)`. Then the rationalizations `(Rf_! K) ⊗ E` and
`(Rf_! K') ⊗ E` of their integral compact-support direct images are canonically isomorphic: the
integral compact-support direct image is an exact `𝒪_E`-linear functor, so it extends to the
rationalizations (`CategoryTheory.Rationalization.map`), and the extension identifies both objects
with its value on the common rationalization. -/
theorem nonempty_iso_fromIntegral_integralRightDerivedLowerShriek {f : X ⟶ Y}
    (c : Compactification f) {K K' : 𝐃𝐜(X)}
    (e : (DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj K ≅
      (DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj K') :
    Nonempty ((DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj
        ((integralRightDerivedLowerShriek l E c).obj K) ≅
      (DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj
        ((integralRightDerivedLowerShriek l E c).obj K')) :=
  ⟨(Rationalization.mapFac 𝐌 (integralRightDerivedLowerShriek l E c)).symm.app K ≪≫
    (rationalRightDerivedLowerShriek l E c).mapIso e ≪≫
    (Rationalization.mapFac 𝐌 (integralRightDerivedLowerShriek l E c)).app K'⟩

end Integral

/-! ### The rational exchange map -/

section Exchange

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The completed compact-support exchange map, restricted to the integral stage: a natural
transformation `(Lg^* Rf_!(c) K)^ ⟶ (Rf'_!(c') Lg'^* K)^` of functors
`D_comp(X_proét, 𝒪_E) ⥤ D_comp(Y'_proét, 𝒪_E)`
(`AlgebraicGeometry.ProEtale.completedRightDerivedLowerShriekOfCompactificationBaseChangeMap`). -/
noncomputable def integralRightDerivedLowerShriekOfCompactificationBaseChangeMap
    (sq : IsPullback g' f' f g) (c : Compactification f) :
    integralOperation l E (Rf_!(c)[ModuleCat.{u + 1} 𝐎] ⋙ L((g)^*[ModuleCat.{u + 1} 𝐎])) ⟶
      integralOperation l E (L((g')^*[ModuleCat.{u + 1} 𝐎]) ⋙
        Rf_!(c.ofIsPullback sq)[ModuleCat.{u + 1} 𝐎]) :=
  Functor.whiskerLeft (DerivedCategoryDerivedCompleteIntegral.ι _ l E)
    ((Functor.associator _ _ _).hom ≫
      completedRightDerivedLowerShriekOfCompactificationBaseChangeMap
        (PadicAlgCl.exists_mem_nonZeroDivisors_maximalIdealShrink_eq_span.{w, u} l E) sq c ≫
      (Functor.associator _ _ _).inv)

lemma integralRightDerivedLowerShriekOfCompactificationBaseChangeMap_app
    (sq : IsPullback g' f' f g) (c : Compactification f) (K : 𝐃𝐜(X)) :
    (integralRightDerivedLowerShriekOfCompactificationBaseChangeMap l E sq c).app K =
      (DerivedCategoryDerivedCompleteIntegral.completion _ l E).map
        ((rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} 𝐎) sq
          c).app ((DerivedCategoryDerivedCompleteIntegral.ι _ l E).obj K)) := by
  simp only [integralRightDerivedLowerShriekOfCompactificationBaseChangeMap,
    Functor.whiskerLeft_app, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id]
  exact completedRightDerivedLowerShriekOfCompactificationBaseChangeMap_app _ sq c _

/-- The rational compact-support exchange map `Lg^* Rf_!(c) ⟶ Rf'_!(c') Lg'^*` on the rational
stage `D_comp(X_proét, E)`, the transport to the rationalizations
(`CategoryTheory.Rationalization.mapNatTrans`) of the integral exchange map
`AlgebraicGeometry.ProEtale.integralRightDerivedLowerShriekOfCompactificationBaseChangeMap`
(blueprint `prop-weil-pbc-rational-transport`). -/
noncomputable def rationalRightDerivedLowerShriekOfCompactificationBaseChangeMap
    (sq : IsPullback g' f' f g) (c : Compactification f) :
    Rationalization.map 𝐌
        (integralOperation l E (Rf_!(c)[ModuleCat.{u + 1} 𝐎] ⋙ L((g)^*[ModuleCat.{u + 1} 𝐎]))) ⟶
      Rationalization.map 𝐌 (integralOperation l E (L((g')^*[ModuleCat.{u + 1} 𝐎]) ⋙
        Rf_!(c.ofIsPullback sq)[ModuleCat.{u + 1} 𝐎])) :=
  Rationalization.mapNatTrans 𝐌
    (integralRightDerivedLowerShriekOfCompactificationBaseChangeMap l E sq c)

/-- Blueprint `thm-cbc-finite-extension`: Compact-support base change over a finite extension.

For a finite extension `E/ℚ_ℓ`, a cartesian square `g' ≫ f = f' ≫ g` with `g` arbitrary and a
compactification `c` of `f` (`def-cbc-compact-support-square`), and an object of the rational
stage `D_comp(X_proét, E)` (`def-weil-pbc-rational-category`) given by an integral lattice
`K ∈ D_comp(X_proét, 𝒪_E)` whose reductions `K_n = K ⊗ᴸ 𝒪_E/𝔪_Eⁿ` carry étale-origin witnesses,
the rational compact-support exchange map `Lg^* Rf_! K ⟶ Rf'_! Lg'^* K` is an isomorphism in
`D_comp(Y'_proét, E)`. It is natural, being a component of a natural transformation, and it
does not depend on the lattice: it is the component at the rationalization of `K` of a natural
transformation of functors on the rational stage
(`AlgebraicGeometry.ProEtale.rationalRightDerivedLowerShriekOfCompactificationBaseChangeMap`).

The isomorphism is transported from the integral one, `thm-cbc-complete-proetale`
(`isIso_completedRightDerivedLowerShriekOfCompactificationBaseChangeMap_app`),
along the rationalization (`prop-weil-pbc-rational-transport`). -/
theorem isIso_rationalRightDerivedLowerShriekOfCompactificationBaseChangeMap_app
    (sq : IsPullback g' f' f g) (c : Compactification f) (K : 𝐃𝐜(X))
    (Kn : ∀ n : ℕ, _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (𝐎 ⧸ PadicAlgCl.maximalIdealShrink l E ^ n))))
    (η : ∀ n : ℕ, (DerivedCategoryDerivedCompleteIntegral.ι _ l E).obj K ⟶
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X)
        (Ideal.Quotient.mk (PadicAlgCl.maximalIdealShrink l E ^ n))).obj (Kn n))
    (hη : ∀ n : ℕ, Sheaf.IsDerivedBaseChange (η n))
    (hKn : ∀ n : ℕ, DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (𝐎 ⧸ PadicAlgCl.maximalIdealShrink l E ^ n)) X (Kn n)) :
    IsIso ((rationalRightDerivedLowerShriekOfCompactificationBaseChangeMap l E sq c).app
      ((DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj K)) := by
  have : ∀ n : ℕ, Finite (𝐎 ⧸ PadicAlgCl.maximalIdealShrink l E ^ n) := fun n ↦
    .of_equiv _ (Ideal.quotientEquiv _ _ (PadicAlgCl.shrinkRingEquiv l E)
      (by rw [PadicAlgCl.maximalIdealShrink, Ideal.map_pow])).toEquiv
  have h := isIso_completedRightDerivedLowerShriekOfCompactificationBaseChangeMap_app
    (PadicAlgCl.exists_mem_nonZeroDivisors_maximalIdealShrink_eq_span.{w, u} l E) sq c _ K.2
    Kn η hη hKn
  rw [completedRightDerivedLowerShriekOfCompactificationBaseChangeMap_app] at h
  have h' : IsIso ((integralRightDerivedLowerShriekOfCompactificationBaseChangeMap l E sq
      c).app K) := by
    rw [integralRightDerivedLowerShriekOfCompactificationBaseChangeMap_app]
    exact h
  rw [rationalRightDerivedLowerShriekOfCompactificationBaseChangeMap]
  erw [Rationalization.mapNatTrans_app]
  infer_instance

end Exchange

end AlgebraicGeometry.ProEtale
