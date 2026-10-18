/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.BaseChange.DerivedUnboundedPlus
public import WeilConjectures.SixFunctors.Etale.FieldBaseChange.Theorem
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality

/-!
# Base change towards spectra of fields, for arbitrary schemes and complexes

This file extends `AlgebraicGeometry.Etale.universalBaseChangeProperty_of_field` (blueprint
`lem-kun-0f1i`, for `X` locally of finite type over `K`) to arbitrary `K`-schemes `X` — the
question is local on `X`, and an affine `X` is the limit of affine schemes of finite type over
`K` (blueprint `lem-kun-0ezt`) — and to bounded below complexes: the derived base change map
`Lf'^* Rg_* F ⟶ Rh_* Le^* F` is an isomorphism for every `F ∈ D⁺(T_ét, Λ)`
(`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_field`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Base change towards spectra of fields for affine schemes: for an affine scheme `U` over a
field `K`, the base change `U ×_K S' ⟶ S'` satisfies the base-change property in every degree.
Write `U` as a cofiltered limit of affine schemes `U_i` of finite type over `K` with affine
transition morphisms; then `U ×_K S'` is the limit of the `U_i ×_K S'`, whose base-change
maps are isomorphisms by `AlgebraicGeometry.Etale.universalBaseChangeProperty_of_field`, and
`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isLimit_left` passes to the limit. -/
theorem Etale.baseChangeProperty_pullback_snd_of_isAffine [Finite Λ] {K : Type u} [Field K]
    [HasInvertibleExponent Λ (Spec (.of K))] {U S' : Scheme.{u}} [IsAffine U]
    (a : U ⟶ Spec (.of K)) (b : S' ⟶ Spec (.of K)) (q : ℤ) :
    Etale.BaseChangeProperty Λ (pullback.snd a b) q := by
  obtain ⟨I, _, _, D, t, π, ⟨hc⟩, -, hD, ht, hπ⟩ :=
    Scheme.exists_isLimit_finiteType_of_isAffine a
  intro T Y g e h _ _ sq F
  have : Nonempty I := IsCofiltered.nonempty
  have : IsConnected I := IsCofiltered.isConnected I
  have (i j : I) (φ : i ⟶ j) : IsAffineHom ((Over.lift D t ⋙ Over.pullback b).map φ).left :=
    MorphismProperty.overPullbackMap _ _ (hD φ)
  refine Etale.isIso_baseChangeHomologyMap_of_isLimit_left Λ g (Over.lift D t ⋙ Over.pullback b)
    ((Over.pullback b).mapCone (Over.liftCone D t (Cone.mk U π) a hπ))
    (isLimitOfPreserves (Over.forget S')
      (isLimitOfPreserves (Over.pullback b) (Over.isLimitLiftCone D t _ a hπ hc)))
    (fun _ ↦ pullback.fst g _) (fun _ ↦ pullback.snd g _)
    (fun _ ↦ IsPullback.of_hasPullback _ _) e h sq F q fun i ↦ ?_
  exact Etale.universalBaseChangeProperty_of_field Λ (t.app i) q b (pullback.fst _ _)
    (pullback.snd _ _) (IsPullback.of_hasPullback _ _) g _ _ _ F

/-- Base change towards spectra of fields for affine schemes, for an arbitrary cartesian square:
if `X'` is the base change of an affine `K`-scheme `U` along `b : S' ⟶ Spec K`, then
`f' : X' ⟶ S'` satisfies the base-change property in every degree. -/
theorem Etale.baseChangeProperty_of_isPullback_of_isAffine [Finite Λ] {K : Type u} [Field K]
    [HasInvertibleExponent Λ (Spec (.of K))] {U X' S' : Scheme.{u}} [IsAffine U]
    {a : U ⟶ Spec (.of K)} {b : S' ⟶ Spec (.of K)} {p : X' ⟶ U} {f' : X' ⟶ S'}
    (sq : IsPullback p f' a b) (q : ℤ) :
    Etale.BaseChangeProperty Λ f' q := by
  rw [← sq.isoPullback_hom_snd]
  intro T Y g e h _ _ sq' F
  exact Etale.BaseChangeProperty.comp Λ (Etale.baseChangeProperty_of_isIso Λ _ q)
    (Etale.baseChangeProperty_pullback_snd_of_isAffine Λ a b q) g e h sq' F

/-- Base change towards spectra of fields, for arbitrary schemes: if `X'` is the base change of
an arbitrary `K`-scheme `X` along `b : S' ⟶ Spec K`, then `f' : X' ⟶ S'` satisfies the
base-change property in every degree. The question is local on `X'`, which is covered by the
base changes of the affine opens of `X`
(`AlgebraicGeometry.Etale.BaseChangeProperty.of_etale_cover`), and the affine case is
`AlgebraicGeometry.Etale.baseChangeProperty_of_isPullback_of_isAffine`. -/
theorem Etale.baseChangeProperty_of_field [Finite Λ] {K : Type u} [Field K]
    [HasInvertibleExponent Λ (Spec (.of K))] {X X' S' : Scheme.{u}}
    {a : X ⟶ Spec (.of K)} {b : S' ⟶ Spec (.of K)} {p : X' ⟶ X} {f' : X' ⟶ S'}
    (sq : IsPullback p f' a b) (q : ℤ) :
    Etale.BaseChangeProperty Λ f' q := by
  let 𝒰 := X.affineCover
  intro T Y g e h _ _ sq' F
  refine Etale.BaseChangeProperty.of_etale_cover Λ (fun i ↦ pullback.snd (𝒰.f i) p)
    (fun x ↦ ?_) (fun i ↦ pullback.snd (𝒰.f i) p ≫ f') (fun _ ↦ 𝟙 S') (fun _ ↦ rfl)
    (fun i ↦ Etale.baseChangeProperty_of_isPullback_of_isAffine Λ
      ((IsPullback.of_hasPullback (𝒰.f i) p).paste_vert sq) q) g e h sq' F
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq (p x)
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback y x hy
  exact ⟨i, z, hz⟩

/-- Blueprint `lem-kun-0f1i`, derived form: for an arbitrary scheme `X` over a field `K` and
`Λ` finite with exponent invertible in `K`, the derived base change map
`Lf'^* Rg_* F ⟶ Rh_* Le^* F` of the diagram `X ×_K S' ⟵ X ×_K T` over `S' ⟵ T` is an
isomorphism for every bounded below `F`. -/
theorem Etale.isIso_derivedBaseChangeMap_of_field [Finite Λ] {K : Type u} [Field K]
    [HasInvertibleExponent Λ (Spec (.of K))] {X X' S' T Y : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) (b : S' ⟶ Spec (.of K)) (p : X' ⟶ X) (f' : X' ⟶ S')
    (_sq₁ : IsPullback p f' a b) (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S') [QuasiCompact g]
    [QuasiSeparated g] (sq₂ : IsPullback h e f' g)
    (F : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ)
    [F.IsGE n] :
    IsIso ((Etale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) (CommSq.mk sq₂.w.symm)).app F) := by
  refine (Etale.isIso_derivedBaseChangeMap_app_ι_obj_iff (ModuleCat.{u + 1} Λ)
    sq₂.flip.toCommSq ⟨F, n, inferInstance⟩).2 ?_
  rw [← Etale.baseChange_eq_derivedBaseChangeMapPlus]
  exact DerivedCategory.Plus.isIso_app_of_forall_homology _ ⊤
    (fun G _ ↦ (Etale.isIso_baseChange_app_singleFunctor_obj_iff Λ sq₂.flip G).2 fun q ↦
      Etale.baseChangeProperty_of_field Λ _sq₁ q g e h sq₂.flip G)
    (fun K m _ q hq ↦ Etale.isZero_homologyFunctor_baseChangeSource_obj Λ f' g K m q hq)
    (fun K m _ q hq ↦ Etale.isZero_homologyFunctor_baseChangeTarget_obj Λ e h K m q hq) _
    fun _ ↦ trivial

end AlgebraicGeometry
