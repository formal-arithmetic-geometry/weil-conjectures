/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ObjectProperty.Duality
public import WeilConjectures.AlgebraicGeometry.CompactificationDimension
public import WeilConjectures.SixFunctors.Etale.Derived.BidualityGeneric
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPointSupport
public import WeilConjectures.SixFunctors.Etale.Derived.OpenCover
public import WeilConjectures.SixFunctors.Etale.Derived.PointBiduality
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage

/-!
# Verdier biduality on the étale site

Let `k` be an algebraically closed field, `Λ` a finite ring whose exponent is invertible in `k`,
and `X` a separated scheme of finite type over `k`, with structure morphism `a : X ⟶ Spec k`,
dualizing complex `ω_X = Ra^! Λ` and Verdier dual `𝔻_X = RHom(-, ω_X)`. This file proves
that the double-dual morphism `δ_K : K ⟶ 𝔻_X 𝔻_X K` is an isomorphism for every `K` in
`Dctf(X, Λ)`, so that `𝔻_X` is an anti-equivalence of `Dctf(X, Λ)`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app` (`sk-prop-sf-biduality-general`,
  `thm-weil-etale-geometric-biduality`): `δ_K` is an isomorphism on `Dctf(X, Λ)`; hence
  `AlgebraicGeometry.Etale.nonempty_iso_verdierDual_verdierDual`.
- `AlgebraicGeometry.Etale.verdierDualEquivalence` (`sk-prop-sf-biduality-general`): the
  anti-equivalence `𝔻_X : Dctf(X, Λ)ᵒᵖ ≌ Dctf(X, Λ)`.

## Proof

As in the blueprint (`thm-weil-etale-geometric-biduality`), by induction on `d = dim X`,
simultaneously for all algebraically closed fields:

1. the assertion is local on `X` (`lem-weil-delta-restriction`), so `X` may be assumed affine,
   and then, by Nagata compactification and extension by zero, proper of dimension `≤ d`;
2. at a nonclosed point `x` of `X`, a coordinate `X ⟶ 𝔸¹_k` sending `x` to the generic point
   has a geometric generic fibre of dimension `< d`, on which `δ` is an isomorphism by
   induction, and the restriction of `δ_K` to it is `δ` of the restriction
   (`lem-weil-geometric-generic-duality`): so `δ_K` is an isomorphism at `x`;
3. the cone of `δ_K` is constructible, hence supported on finitely many closed points, and
   `Ra_* δ_K` is an isomorphism (`lem-weil-delta-proper-pushforward`, biduality at the point
   `lem-weil-coefficient-frobenius`); so `δ_K` is an isomorphism.

The hypothesis that `k` is algebraically closed is that of the blueprint (`sk-def-sf-setting`,
where `k = 𝔽̄_q`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

section Induction

variable {Λ}

/-- The double-dual morphism only depends on the structure morphism, not on the instances
carried along: for `a = b`, a functor `G` sends `δ_K` of `a` and of `b` to isomorphisms
together. -/
lemma isIso_map_verdierDualDoubleDual_app_congr {X S : Scheme.{u}} {a b : X ⟶ S} (h : a = b)
    [HasCompactification a] [HasCompactification b] {D : Type*} [Category D]
    (G : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤ D)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (G.map ((verdierDualDoubleDual (ModuleCat.{u + 1} Λ) a).app K)) ↔
      IsIso (G.map ((verdierDualDoubleDual (ModuleCat.{u + 1} Λ) b).app K)) := by
  subst h
  rfl

/-- Biduality for a proper `X`, assuming it in lower dimensions: at the nonclosed points by the
induction hypothesis, and globally by `Ra_* δ_K = δ_{Ra_* K}` and biduality at the point. -/
theorem isIso_verdierDualDoubleDual_app_of_isProper {d : ℕ} (IH : ∀ d' < d, BidualityUpTo Λ d')
    {k : Type u} [Field k] [IsAlgClosed k] [HasInvertibleExponent Λ (Spec (.of k))]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) [IsProper a]
    (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    IsIso ((verdierDualDoubleDual (ModuleCat.{u + 1} Λ) a).app K) := by
  have hDD := constructibleFiniteTor_verdierDual Λ a (constructibleFiniteTor_verdierDual Λ a hK)
  refine isIso_of_isIso_rightDerivedLowerStar_map_of_not_isClosed Λ a hK.1 hDD.1 _
    (fun x hx q ↦ isIso_sheafFiber_map_verdierDualDoubleDual_app_of_not_isClosed Λ d IH a hX hK
      x hx q) ?_
  have hpt := isIso_verdierDualDoubleDual_app_id_of_isSepClosed Λ
    (constructibleFiniteTor_rightDerivedLowerStar Λ a (𝟙 _) a (Category.comp_id a) hK)
  have h := (isIso_rightDerivedLowerStar_map_verdierDualDoubleDual_app_iff_of_finite Λ a
    (𝟙 (Spec (.of k))) K).2 hpt
  exact (isIso_map_verdierDualDoubleDual_app_congr (Category.comp_id a)
    R((a)_*[ModuleCat.{u + 1} Λ]) K).1 h

/-- Biduality for a separated `X` of finite type over `k` with `dim X ≤ d`, assuming it in lower
dimensions: on the affine opens of `X`, which are open in proper schemes of dimension `≤ d`. -/
theorem bidualityUpTo (d : ℕ) : BidualityUpTo Λ d := by
  induction d using Nat.strong_induction_on with | _ d IH => ?_
  intro k _ _ _ X a _ _ _ hX K hK
  refine isIso_of_forall_isIso_leftDerivedUpperStar_map Λ (fun U : X.affineOpens ↦ U.1) ?_ _
    fun U ↦ ?_
  · exact eq_top_iff.2 fun x _ ↦ by
      obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
        (show x ∈ (⊤ : X.Opens) from trivial)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU⟩, hxU⟩
  have : HasInvertibleExponent Λ X := .of_hom a
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace a
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated a
  -- restrict to the affine open `U`
  have hU : constructibleFiniteTor (ModuleCat.{u + 1} Λ) U.1
      ((L((U.1.ι)^*[ModuleCat.{u + 1} Λ])).obj K) :=
    constructibleFiniteTor_leftDerivedUpperStar _ U.1.ι hK
  rw [isIso_leftDerivedUpperStar_map_verdierDualDoubleDual_app_iff_of_finite Λ U.1.ι a K]
  generalize (L((U.1.ι)^*[ModuleCat.{u + 1} Λ])).obj K = KU at hU
  have : IsAffine U.1 := U.2
  have hUd : topologicalKrullDim U.1 ≤ (d : WithBot ℕ∞) :=
    (topologicalKrullDim_subspace_le X U.1).trans hX
  -- compactify `U` inside a proper `Y` of dimension `≤ d`
  obtain ⟨Y, b, j, hb, hj, hjq, hjb, hY⟩ :=
    exists_isProper_isOpenImmersion_topologicalKrullDim_le (U.1.ι ≫ a) d hUd
  have : HasInvertibleExponent Λ Y := .of_hom b
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace b
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated b
  obtain ⟨hbc, p, q, hpq⟩ := hU
  have hK' := constructibleTorAmplitudeIn_mapDerivedCategory_openImmersionLowerShriek Λ j p q
    ⟨⟨hbc, _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn hpq⟩, hpq⟩
  have hδ := isIso_verdierDualDoubleDual_app_of_isProper IH b hY (K := D((j)_!open[_]).obj KU)
    ⟨hK'.1.1, p, q, hK'.2⟩
  -- restrict back along `j`
  have h₁ := (isIso_leftDerivedUpperStar_map_verdierDualDoubleDual_app_iff_of_finite Λ j b
    (D((j)_!open[_]).obj KU)).1 inferInstance
  have h₂ := (isIso_map_verdierDualDoubleDual_app_congr hjb (𝟭 _) _).1 h₁
  exact (NatTrans.isIso_app_iff_of_iso _ (asIso
    ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction _ j).unit.app KU))).2 h₂

end Induction

section Field

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsAlgClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))] {X : Scheme.{u}} (a : X ⟶ Spec (.of k))
  [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] [HasCompactification a]

/-- Blueprint `sk-prop-sf-biduality-general`: General Verdier biduality; blueprint
`thm-weil-etale-geometric-biduality`: Finite-stage étale Verdier biduality.

For `X` separated of finite type over an algebraically closed field `k` and a finite coefficient
ring `Λ` whose exponent is invertible on `k`, the double-dual morphism `δ_K : K ⟶ 𝔻_X 𝔻_X K`
(`AlgebraicGeometry.Etale.verdierDualDoubleDual`) is an isomorphism for every `K` in
`Dctf(X, Λ)`. The proof is by induction on `dim X`, through the geometric generic fibres of the
maps `X ⟶ 𝔸¹_k` (`AlgebraicGeometry.Etale.bidualityUpTo`). -/
theorem isIso_verdierDualDoubleDual_app
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    IsIso ((verdierDualDoubleDual (ModuleCat.{u + 1} Λ) a).app K) := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le a
  exact bidualityUpTo d k X a hd K hK

/-- Blueprint `sk-prop-sf-biduality-general`: General Verdier biduality.

For `X` separated of finite type over an algebraically closed field `k` and a finite coefficient
ring `Λ` whose exponent is invertible on `k`, `K ≅ 𝔻_X 𝔻_X K` for every object `K` of
`Dctf(X, Λ)`, by the double-dual morphism
(`AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app`). -/
theorem nonempty_iso_verdierDual_verdierDual
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    Nonempty (K ≅ (verdierDual (ModuleCat.{u + 1} Λ) a).obj
      (op ((verdierDual (ModuleCat.{u + 1} Λ) a).obj (op K)))) :=
  have := isIso_verdierDualDoubleDual_app Λ a hK
  ⟨asIso ((verdierDualDoubleDual (ModuleCat.{u + 1} Λ) a).app K)⟩

/-- Blueprint `sk-prop-sf-biduality-general`: General Verdier biduality.

For `X` separated of finite type over an algebraically closed field `k` and a finite coefficient
ring `Λ` whose exponent is invertible on `k`, the Verdier dual `𝔻_X = RHom(-, ω_X)` restricts to
a contravariant anti-equivalence `Dctf(X, Λ)ᵒᵖ ≌ Dctf(X, Λ)`, with quasi-inverse `𝔻_X` itself:
`𝔻_X` preserves `Dctf(X, Λ)` (`AlgebraicGeometry.Etale.constructibleFiniteTor_verdierDual`) and
the unit and the counit are the double-dual isomorphisms `δ_K : K ≅ 𝔻_X 𝔻_X K`
(`AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app`). -/
noncomputable def verdierDualEquivalence :
    (DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X)ᵒᵖ ≌
      DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X :=
  (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).liftDualEquivalence
    (verdierDual (ModuleCat.{u + 1} Λ) a) (fun _ hK ↦ constructibleFiniteTor_verdierDual Λ a hK)
    (verdierDualDoubleDual (ModuleCat.{u + 1} Λ) a)
    (fun _ hK ↦ isIso_verdierDualDoubleDual_app Λ a hK)

end Field

end Etale

end AlgebraicGeometry
