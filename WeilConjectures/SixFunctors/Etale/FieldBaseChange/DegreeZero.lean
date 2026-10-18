/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import WeilConjectures.SixFunctors.BaseChange.UniversalHomeomorphism
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Base change in degree zero along `X ×_K S' ⟶ S'`

For a scheme `X` locally of finite type over a field `K`, the degree-zero base-change property
holds universally for `X ⟶ Spec K`
(`AlgebraicGeometry.Etale.universalBaseChangeProperty_zero_of_field`): for every base change
`X' = X ×_K S' ⟶ S'`, every quasi-compact quasi-separated `g : T ⟶ S'` and every sheaf `F` on
`T`, the map `p⁻¹ g_* F ⟶ h_* e⁻¹ F` is an isomorphism.

Following the proof of blueprint `lem-kun-0f1i`: after the base change to the perfect closure
`K^{perf}` of `K` and the passage to the reduction of `X_{K^{perf}}` — both universal
homeomorphisms, along which étale cohomology and the base-change maps are invariant — the
morphism to the base is flat, locally of finite presentation and has geometrically reduced
fibres, so the degree-zero base change property holds by blueprint `lem-kun-0eys`
(`AlgebraicGeometry.Etale.universalBaseChangeProperty_zero`).

## Main statements

- `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isUniversalHomeomorphism_target`:
  replacing `T` by `T'` along a universal homeomorphism `T' ⟶ T`.
- `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isUniversalHomeomorphism_source`:
  replacing `X` by `X₁` along a universal homeomorphism `X₁ ⟶ X`.
- `AlgebraicGeometry.Etale.universalBaseChangeProperty_zero_of_perfectField`: the case of a
  perfect field.
- `AlgebraicGeometry.Etale.universalBaseChangeProperty_zero_of_field`: the general case.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Replacing the target `T` of `g` by `T'` along a universal homeomorphism `π : T' ⟶ T`: if the
base-change map of a Cartesian square over `π ≫ g` is an isomorphism at `π⁻¹ F`, then the
base-change map of a Cartesian square over `g` is an isomorphism at `F`.

The direct image along `π` identifies the base-change map over `g` at `π_* π⁻¹ F` with the one
over `π ≫ g` at `π⁻¹ F`
(`AlgebraicGeometry.Etale.nonempty_arrowIso_baseChangeHomologyMap_lowerStar`), and
`F ⟶ π_* π⁻¹ F` is an isomorphism, `π⁻¹` being an equivalence
(`AlgebraicGeometry.Etale.isEquivalence_upperStar`). -/
theorem Etale.isIso_baseChangeHomologyMap_of_isUniversalHomeomorphism_target
    {X S T Y T' Y' : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}
    {e' : Y' ⟶ T'} {h' : Y' ⟶ X} (sq : IsPullback e h g p) (π : T' ⟶ T)
    [IsUniversalHomeomorphism π] (sq' : IsPullback e' h' (π ≫ g) p) (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsIso (Etale.baseChangeHomologyMap Λ sq' q ((π)^*[ModuleCat.{u + 1} Λ].obj F))) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) := by
  obtain ⟨φ⟩ := Etale.nonempty_arrowIso_baseChangeHomologyMap_lowerStar Λ sq π sq' q
    ((π)^*[ModuleCat.{u + 1} Λ].obj F)
  have : IsIso (Etale.baseChangeHomologyMap Λ sq q
      ((π)_*[ModuleCat.{u + 1} Λ].obj ((π)^*[ModuleCat.{u + 1} Λ].obj F))) :=
    (Arrow.isIso_iff_isIso_of_isIso φ.hom).2 hF
  have := Etale.isEquivalence_upperStar (ModuleCat.{u + 1} Λ) π
  have hw := Etale.baseChangeHomologyMap_naturality Λ sq q
    ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) π).unit.app F)
  simp only [Functor.id_obj, Functor.comp_obj] at hw
  have : IsIso (Etale.baseChangeHomologyMap Λ sq q F ≫ (Etale.baseChangeTargetFunctor Λ e h q).map
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) π).unit.app F)) := by
    rw [hw]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((Etale.baseChangeTargetFunctor Λ e h q).map
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) π).unit.app F))

/-- Replacing the source `X` of `p` by `X₁` along a universal homeomorphism `p₁ : X₁ ⟶ X`: if
the base-change map of the Cartesian square on `p₁ ≫ p₂` obtained by pasting a Cartesian square
on `p₁` to a Cartesian square on `p₂` is an isomorphism at `F`, so is the base-change map of the
square on `p₂`.

By the pasting law `AlgebraicGeometry.Etale.baseChange_app_paste_horiz`, the former is the
pullback along `p₁` of the latter followed by the base-change map of the square on `p₁`, which
is an isomorphism
(`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_isUniversalHomeomorphism`);
and the pullback along `p₁` is exact and an equivalence, hence reflects isomorphisms. -/
theorem Etale.isIso_baseChangeHomologyMap_of_isUniversalHomeomorphism_source
    {X Z S T Y₂ Y : Scheme.{u}} {g : T ⟶ S} {p₂ : Z ⟶ S} {e₂ : Y₂ ⟶ T} {h₂ : Y₂ ⟶ Z}
    {p₁ : X ⟶ Z} {e₁ : Y ⟶ Y₂} {h₁ : Y ⟶ X} [IsUniversalHomeomorphism p₁]
    (sq₂ : IsPullback e₂ h₂ g p₂) (sq₁ : IsPullback e₁ h₁ h₂ p₁)
    (sq : IsPullback (e₁ ≫ e₂) h₁ g (p₁ ≫ p₂)) (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsIso (Etale.baseChangeHomologyMap Λ sq q F)) :
    IsIso (Etale.baseChangeHomologyMap Λ sq₂ q F) := by
  rw [Etale.isIso_baseChangeHomologyMap_iff] at hF ⊢
  rw [Etale.baseChange_app_paste_horiz Λ sq₂.toCommSq sq₁.toCommSq sq.toCommSq] at hF
  simp only [Functor.map_comp] at hF
  have : IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq₁.toCommSq).app
      (((e₂)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
    rw [Etale.baseChange_eq_derivedBaseChangeMapPlus]
    have := Etale.isIso_derivedBaseChangeMapPlus_of_isUniversalHomeomorphism
      (ModuleCat.{u + 1} Λ) sq₁
    infer_instance
  simp only [isIso_comp_left_iff, isIso_comp_right_iff] at hF
  have := (NatIso.isIso_map_iff
    (((p₁)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso q) _).2 hF
  rw [Functor.comp_map] at this
  have := Etale.isEquivalence_upperStar (ModuleCat.{u + 1} Λ) p₁
  exact isIso_of_reflects_iso _ (p₁)^*[ModuleCat.{u + 1} Λ]

/-- The degree-zero base-change property holds universally for a scheme locally of finite type
over a perfect field `L`.

The reduction `ι : X_{red} ⟶ X` is a universal homeomorphism, and `X_{red} ⟶ Spec L` is flat
(over a field), locally of finite presentation (locally of finite type over a noetherian base)
and geometrically reduced (reduced over a perfect field), so it satisfies the degree-zero
base-change property universally (`AlgebraicGeometry.Etale.universalBaseChangeProperty_zero`).
For a base change `p' : X' ⟶ S'` of `X ⟶ Spec L`, the base change `ι' ≫ p'` of
`X_{red} ⟶ Spec L` then satisfies it, and
`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isUniversalHomeomorphism_source`
transfers it along the universal homeomorphism `ι'`. -/
theorem Etale.universalBaseChangeProperty_zero_of_perfectField {L : Type u} [Field L]
    [PerfectField L] {X : Scheme.{u}} (a : X ⟶ Spec (.of L)) [LocallyOfFiniteType a] :
    Etale.UniversalBaseChangeProperty Λ a 0 := by
  have : Surjective X.nilradical.subschemeι := by
    constructor
    rw [← Set.range_eq_univ, Scheme.IdealSheafData.range_subschemeι, Scheme.support_nilradical]
    rfl
  have : GeometricallyReduced (X.nilradical.subschemeι ≫ a) := .of_perfectField _
  have : LocallyOfFinitePresentation (X.nilradical.subschemeι ≫ a) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance
  have hred := Etale.universalBaseChangeProperty_zero Λ (X.nilradical.subschemeι ≫ a)
  intro S' X' s b p' hp T Y g e h _ _ sq F
  have hbc : Etale.BaseChangeProperty Λ _ 0 := hred s _ _
    ((IsPullback.of_hasPullback b X.nilradical.subschemeι).flip.paste_vert hp)
  have sq₁ := IsPullback.of_hasPullback h (pullback.fst b X.nilradical.subschemeι)
  exact Etale.isIso_baseChangeHomologyMap_of_isUniversalHomeomorphism_source Λ sq sq₁
    (sq₁.paste_horiz sq) 0 F (hbc g _ _ (sq₁.paste_horiz sq) F)

/-- The degree-zero base-change property holds universally for a scheme locally of finite type
over a field.

Let `L` be the perfect closure of `K` in an algebraic closure, so that `Spec L ⟶ Spec K` is a
universal homeomorphism. For a base change `p' : X' ⟶ S'` of `a`, a quasi-compact
quasi-separated `g : T ⟶ S'` and a Cartesian square over `g`, base change everything along
`π : S'_L ⟶ S'`. By
`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isUniversalHomeomorphism_target` it
suffices to treat the square over `T_L ⟶ T ⟶ S'`, which by
`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_iff_of_isIntegralHom` reduces to the square
over `T_L ⟶ S'_L` for the base change `X'_L ⟶ S'_L` of `X_L ⟶ Spec L`; the latter satisfies the
degree-zero base-change property by
`AlgebraicGeometry.Etale.universalBaseChangeProperty_zero_of_perfectField`. -/
theorem Etale.universalBaseChangeProperty_zero_of_field {K : Type u} [Field K] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] :
    Etale.UniversalBaseChangeProperty Λ a 0 := by
  have : IsUniversalHomeomorphism (Spec.map (CommRingCat.ofHom
      (algebraMap K (perfectClosure K (AlgebraicClosure K))))) :=
    Algebra.IsUniversalHomeomorphism.isUniversalHomeomorphism
  have hL := Etale.universalBaseChangeProperty_zero_of_perfectField Λ (pullback.snd a
    (Spec.map (CommRingCat.ofHom (algebraMap K (perfectClosure K (AlgebraicClosure K))))))
  intro S' X' s b p' hp T Y g e h _ _ sq F
  set πK := Spec.map (CommRingCat.ofHom (algebraMap K (perfectClosure K (AlgebraicClosure K))))
  have hπ := IsPullback.of_hasPullback p' (pullback.fst s πK)
  have sq'' := IsPullback.of_hasPullback (pullback.snd g (pullback.fst s πK))
    (pullback.snd p' (pullback.fst s πK))
  have hcomp : IsPullback (pullback.lift (pullback.fst p' (pullback.fst s πK) ≫ b)
      (pullback.snd p' (pullback.fst s πK) ≫ pullback.snd s πK)
      (by rw [Category.assoc, hp.w, ← Category.assoc, pullback.condition, Category.assoc,
        Category.assoc, pullback.condition]) ≫ pullback.fst a πK)
      (pullback.snd p' (pullback.fst s πK)) a (pullback.snd s πK ≫ πK) := by
    rw [pullback.lift_fst, ← pullback.condition]
    exact hπ.paste_horiz hp
  have hbc : Etale.BaseChangeProperty Λ _ 0 := hL _ _ _ (hcomp.of_right (pullback.lift_snd _ _ _)
    (IsPullback.of_hasPullback a πK))
  have hk (k : _ ⟶ S') (hk : pullback.snd g (pullback.fst s πK) ≫ pullback.fst s πK = k)
      (sqk : IsPullback (pullback.fst (pullback.snd g (pullback.fst s πK))
        (pullback.snd p' (pullback.fst s πK))) (pullback.snd (pullback.snd g (pullback.fst s πK))
        (pullback.snd p' (pullback.fst s πK)) ≫ pullback.fst p' (pullback.fst s πK)) k p') G :
      IsIso (Etale.baseChangeHomologyMap Λ sqk 0 G) := by
    subst hk
    exact (Etale.isIso_baseChangeHomologyMap_iff_of_isIntegralHom Λ _ hπ sq'' sqk 0 G).2
      (hbc _ _ _ sq'' G)
  refine Etale.isIso_baseChangeHomologyMap_of_isUniversalHomeomorphism_target Λ sq
    (pullback.fst g (pullback.fst s πK)) ?_ 0 F (hk _ pullback.condition.symm _ _)
  rw [pullback.condition]
  exact (sq''.flip.paste_horiz hπ).flip

end AlgebraicGeometry
