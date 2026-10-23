/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineKunneth
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerAffineLine
public import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnboundedPlus
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived

/-!
# Cohomology of smooth schemes after a strictly henselian base change

Let `K` be a separably closed field, `R` a strictly henselian local ring and `g : Spec R ⟶ Spec K`
a morphism. The étale cohomology of `Spec R` with coefficients in a finite ring `Λ` is `Λ` in
degree zero and vanishes otherwise, so `Rg_* Λ ≅ Λ_K`
(`AlgebraicGeometry.Etale.nonempty_rightDerivedLowerStar_constantComplex_iso_of_isStrictlyHenselianLocalRing`).
By smooth base change, for a smooth `p : X ⟶ Spec K` with base change `Y = X ×_K Spec R`, the
étale cohomology of `Y` with coefficients `Λ` is that of `X`
(`AlgebraicGeometry.Etale.nonempty_cohomology_constantComplex_iso_of_isPullback`).

Separably closed fields are strictly henselian, so this also compares the cohomology of `X` with
that of its base change to an algebraic closure of `K`. This is the input of the computation of
the stalks of the direct images of `𝔸¹` and `𝔾ₘ` over a base (blueprint `sk-prop-a1-kummer`):
over a strictly henselian local ring with a separably closed subfield, the cohomology of `𝔸¹`
and `𝔾ₘ` is that over an algebraically closed field.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

/-- The spectrum of a local ring is connected: every point specializes to the closed point. -/
lemma connectedSpace_spec_of_isLocalRing (R : Type u) [CommRing R] [IsLocalRing R] :
    ConnectedSpace (Spec (.of R)) := by
  have : PreconnectedSpace (PrimeSpectrum R) := ⟨isPreconnected_of_forall
    (IsLocalRing.closedPoint R) fun y _ ↦ ⟨closure {y}, Set.subset_univ _,
      specializes_iff_mem_closure.1 (IsLocalRing.specializes_closedPoint y),
      subset_closure (Set.mem_singleton y),
      (IsIrreducible.isConnected (IsIrreducible.closure isIrreducible_singleton)).isPreconnected⟩⟩
  have : ConnectedSpace (PrimeSpectrum R) :=
    { toPreconnectedSpace := this, toNonempty := ⟨IsLocalRing.closedPoint R⟩ }
  exact inferInstanceAs (ConnectedSpace (PrimeSpectrum R))

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

section StrictlyHenselian

variable (A : Type u) [CommRing A] [IsStrictlyHenselianLocalRing A]

/-- The étale cohomology of the spectrum of a strictly henselian local ring vanishes in nonzero
degrees. -/
lemma isZero_cohomology_constantComplex_of_isStrictlyHenselianLocalRing (q : ℤ) (hq : q ≠ 0) :
    IsZero ((cohomology (ModuleCat.{u + 1} Λ) (Spec (.of A)) q).obj
      (constantComplex Λ (Spec (.of A)))) := by
  rcases lt_or_gt_of_ne hq with hq | hq
  · exact IsZero.of_iso (isZero_cohomology_singleFunctor_of_neg Λ _ _ hq)
      ((cohomology _ _ q).mapIso (constantComplexIsoSingleFunctorConstantSheaf Λ _))
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, q = ((n + 1 : ℕ) : ℤ) := ⟨q.toNat - 1, by omega⟩
    exact isZero_cohomology_constantComplex_of_subsingleton Λ _ (n + 1)
      (subsingleton_H_of_isStrictlyHenselianLocalRing A _ n)

variable {A} {K : Type u} [Field K] [IsSepClosed K]

/-- For a strictly henselian local ring `R` and a separably closed field `K`, the direct image
of the constant complex along `g : Spec R ⟶ Spec K` is the constant complex: the étale
cohomology of `Spec R` is `Λ` in degree zero. -/
theorem nonempty_rightDerivedLowerStar_constantComplex_iso_of_isStrictlyHenselianLocalRing
    (g : Spec (.of A) ⟶ Spec (.of K)) :
    Nonempty ((R((g)_*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ (Spec (.of A))) ≅
      constantComplex Λ (Spec (.of K))) := by
  have := connectedSpace_spec_of_isLocalRing A
  obtain ⟨e⟩ := nonempty_iso_constantFunctor_rightDerivedGlobalSections_of_isSepClosed Λ
    ((R((g)_*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ (Spec (.of A))))
  obtain ⟨e₂⟩ := nonempty_iso_singleFunctor_of_homology
    ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of A))).obj
      (constantComplex Λ (Spec (.of A))))
    (isZero_cohomology_constantComplex_of_isStrictlyHenselianLocalRing Λ A)
    (cohomologyZeroConstantComplexIso Λ _)
  exact ⟨e ≪≫ (constantFunctor Λ _).mapIso
    ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ g).app _ ≪≫ e₂) ≪≫
      constantFunctorObjSingleIso Λ _⟩

variable [HasInvertibleExponent Λ (Spec (.of K))]

/-- **Cohomology after a strictly henselian base change.** Let `K` be separably closed,
`p : X ⟶ Spec K` smooth, `R` a strictly henselian local ring with a morphism
`g : Spec R ⟶ Spec K`, and `Y = X ×_K Spec R`. Then `Hᵠ(Y, Λ) ≅ Hᵠ(X, Λ)`: by smooth base change
`Rh_* Λ_Y ≅ Lp^* Rg_* Λ ≅ Λ_X` for the projection `h : Y ⟶ X`. -/
theorem nonempty_cohomology_constantComplex_iso_of_isPullback
    (g : Spec (.of A) ⟶ Spec (.of K)) {X Y : Scheme.{u}} (p : X ⟶ Spec (.of K)) [Smooth p]
    (e : Y ⟶ Spec (.of A)) (h : Y ⟶ X) (sq : IsPullback e h g p) (q : ℤ) :
    Nonempty ((cohomology (ModuleCat.{u + 1} Λ) Y q).obj (constantComplex Λ Y) ≅
      (cohomology (ModuleCat.{u + 1} Λ) X q).obj (constantComplex Λ X)) := by
  obtain ⟨n, hn, hΛ, hu⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ)
    (X := Spec (.of K))
  have : IsTorsionSheafOfInvertibleOrder (Spec (.of K))
      (𝟙_ (Sheaf (Spec (.of A)).smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
    IsTorsionSheafOfInvertibleOrder.of_natCast_eq_zero Λ n hn.ne' hΛ hu _
  have hBC : IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
      (constantComplex Λ (Spec (.of A)))) := by
    rw [NatTrans.isIso_app_iff_of_iso _ (constantComplexIsoSingleFunctor Λ _)]
    refine (isIso_derivedBaseChangeMap_app_ι_obj_iff _ sq.toCommSq
      ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj _)).2 ?_
    rw [← Etale.baseChange_eq_derivedBaseChangeMapPlus]
    exact Etale.isIso_baseChange_app_singleFunctor_obj_of_smooth Λ p sq _
  obtain ⟨e₁⟩ :=
    nonempty_rightDerivedLowerStar_constantComplex_iso_of_isStrictlyHenselianLocalRing Λ g
  -- `Rh_* Λ_Y ≅ Λ_X`
  let E : (R((h)_*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ Y) ≅ constantComplex Λ X :=
    (R((h)_*[ModuleCat.{u + 1} Λ])).mapIso (leftDerivedUpperStarConstantComplexIso Λ e).symm ≪≫
      (asIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
        (constantComplex Λ (Spec (.of A))))).symm ≪≫
      (L((p)^*[ModuleCat.{u + 1} Λ])).mapIso e₁ ≪≫ leftDerivedUpperStarConstantComplexIso Λ p
  exact ⟨(_root_.DerivedCategory.homologyFunctor _ q).mapIso
    (((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ h).app _).symm ≪≫
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).mapIso E)⟩

end StrictlyHenselian

end Etale

end AlgebraicGeometry
