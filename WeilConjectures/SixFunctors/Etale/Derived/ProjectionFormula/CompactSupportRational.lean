/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalCoefficient
public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated

/-!
# Compact support at the rational stage does not depend on the integral representative

Let `E` be a finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ` with ring of integers `𝒪_E`. An object of
the rational stage `D_comp(X_ét, E)` (`DerivedCategoryDerivedCompleteRational`) is represented by
derived complete integral objects `K ∈ D_comp(X_ét, 𝒪_E)`, its lattices. This file shows that the
rationalization `(Rf_! K) ⊗ E` of the compactly supported direct image of a lattice `K` depends,
up to a canonical isomorphism, only on the rational object `K ⊗ E` (blueprint
`lem-weil-compact-support-representative-independence`).

Here `Rf_!` is the compactly supported direct image
`AlgebraicGeometry.Etale.rightDerivedLowerShriek`
of `D(X_ét, 𝒪_E)` and `- ⊗ E` is the rationalization `D(Y_ét, 𝒪_E) ⥤ D(Y_ét, 𝒪_E)[1/ℓ]`
(`CategoryTheory.Rationalization.Q`), the Verdier quotient by the objects killed by a nonzero
element of `𝒪_E`. As in the blueprint, the isomorphism comes from the fact that the
`𝒪_E`-linear triangulated functor `Rf_!` descends to the rationalizations
(`CategoryTheory.Rationalization.map`). The target is the rationalization of the whole derived
category rather than of `D_comp(Y_ét, 𝒪_E)`: on the small étale site with discrete coefficients
`Rf_!` need not preserve derived completeness for non-proper `f`
(`AlgebraicGeometry.Etale.derivedComplete_rightDerivedLowerShriek`).

## Main definitions

- `AlgebraicGeometry.Etale.rationalizationRightDerivedLowerShriekIso`
  (`lem-weil-compact-support-representative-independence`)
-/

@[expose] public section

universe w u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The coefficient category `ModuleCat 𝒪_E` of the integral stage. -/
local notation "𝐌" => ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))

set_option hygiene false in
/-- The nonzero elements of `𝒪_E`, inverted by the rationalization. -/
local notation "𝐒" => nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E))

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra ℚ_[l] E]
  [Algebra E (PadicAlgCl l)] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E] [Small.{u + 1} E]

variable {X Y : Scheme.{u}}

noncomputable instance (X : Scheme.{u}) :
    (DerivedCategoryDerivedCompleteIntegral.ι X.smallEtaleTopology l E).CommShift ℤ :=
  inferInstanceAs
    ((DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E).ι.CommShift ℤ)

instance (X : Scheme.{u}) :
    (DerivedCategoryDerivedCompleteIntegral.ι X.smallEtaleTopology l E).IsTriangulated :=
  inferInstanceAs
    (DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E).ι.IsTriangulated

instance (X : Scheme.{u}) :
    (DerivedCategoryDerivedCompleteIntegral.ι X.smallEtaleTopology l E).Linear
      (Shrink.{u + 1} (PadicAlgCl.integers l E)) where
  map_smul _ _ := rfl

/-- The rationalization of `Rf_! (ι K)` for a derived complete `K` is the image of the rational
object `K ⊗ E` under the functor induced by `Rf_! ∘ ι` on rationalizations. -/
noncomputable def rationalizationRightDerivedLowerShriekIsoMap (f : X ⟶ Y) [HasCompactification f]
    (K : DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E) :
    (Rationalization.Q 𝐒 (_root_.DerivedCategory (Sheaf Y.smallEtaleTopology 𝐌))).obj
        ((R(f)_![𝐌]).obj ((DerivedCategoryDerivedCompleteIntegral.ι _ l E).obj K)) ≅
      (Rationalization.map 𝐒 (DerivedCategoryDerivedCompleteIntegral.ι _ l E ⋙ R(f)_![𝐌])).obj
        ((DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj K) :=
  ((Rationalization.mapFac 𝐒 (DerivedCategoryDerivedCompleteIntegral.ι _ l E ⋙ R(f)_![𝐌])).app
    K).symm

/-- Blueprint `lem-weil-compact-support-representative-independence`: Independence of the
integral representative.

Let `K` and `K'` be derived complete objects of `D(X_ét, 𝒪_E)` representing the same object of
the rational stage `D_comp(X_ét, E)`, via an isomorphism `e : K ⊗ E ≅ K' ⊗ E`. Then the
rationalizations `(Rf_! K) ⊗ E` and `(Rf_! K') ⊗ E` of their compactly supported direct images
are canonically isomorphic: `Rf_!` is `𝒪_E`-linear and triangulated, so it descends to the
rationalizations (`CategoryTheory.Rationalization.map`), and the isomorphism is the image of `e`
under the descended functor. -/
noncomputable def rationalizationRightDerivedLowerShriekIso (f : X ⟶ Y) [HasCompactification f]
    {K K' : DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E}
    (e : (DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj K ≅
      (DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj K') :
    (Rationalization.Q 𝐒 (_root_.DerivedCategory (Sheaf Y.smallEtaleTopology 𝐌))).obj
        ((R(f)_![𝐌]).obj ((DerivedCategoryDerivedCompleteIntegral.ι _ l E).obj K)) ≅
      (Rationalization.Q 𝐒 (_root_.DerivedCategory (Sheaf Y.smallEtaleTopology 𝐌))).obj
        ((R(f)_![𝐌]).obj ((DerivedCategoryDerivedCompleteIntegral.ι _ l E).obj K')) :=
  rationalizationRightDerivedLowerShriekIsoMap l E f K ≪≫
    (Rationalization.map 𝐒 (DerivedCategoryDerivedCompleteIntegral.ι _ l E ⋙ R(f)_![𝐌])).mapIso
      e ≪≫ (rationalizationRightDerivedLowerShriekIsoMap l E f K').symm

/-- The isomorphism `AlgebraicGeometry.Etale.rationalizationRightDerivedLowerShriekIso` is
compatible with `Rf_!` on integral morphisms: for `u : K ⟶ K'` whose rationalization is an
isomorphism, it is the rationalization of `Rf_! u`. -/
lemma rationalizationRightDerivedLowerShriekIso_hom_of_map (f : X ⟶ Y) [HasCompactification f]
    {K K' : DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E} (u : K ⟶ K')
    [IsIso ((DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).map u)] :
    (rationalizationRightDerivedLowerShriekIso l E f
        (asIso ((DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).map u))).hom =
      (Rationalization.Q 𝐒 (_root_.DerivedCategory (Sheaf Y.smallEtaleTopology 𝐌))).map
        ((R(f)_![𝐌]).map ((DerivedCategoryDerivedCompleteIntegral.ι _ l E).map u)) := by
  have := (Rationalization.mapFac 𝐒
    (DerivedCategoryDerivedCompleteIntegral.ι _ l E ⋙ R(f)_![𝐌])).inv.naturality u
  simp only [Functor.comp_obj, Functor.comp_map] at this
  simp only [rationalizationRightDerivedLowerShriekIso,
    rationalizationRightDerivedLowerShriekIsoMap,
    Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, Iso.app_inv, Functor.mapIso_hom, asIso_hom,
    Iso.app_hom]
  rw [← reassoc_of% this, Iso.inv_hom_id_app]
  exact Category.comp_id _

end Etale

end AlgebraicGeometry
