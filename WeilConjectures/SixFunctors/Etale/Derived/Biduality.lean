/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ObjectProperty.Duality
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricGenericFibre
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

section Steps

/-- **Locality of isomorphisms in `D(X_ét, Λ)`.** A morphism of `D(X_ét, Λ)` is an isomorphism
as soon as its restrictions to the members of an open cover of `X` are. -/
theorem isIso_of_forall_isIso_leftDerivedUpperStar_map {X : Scheme.{u}} {ι : Type*}
    (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    {K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (f : K ⟶ L) (h : ∀ i, IsIso ((L(((U i).ι)^*[ModuleCat.{u + 1} Λ])).map f)) :
    IsIso f :=
  sorry

/-- Blueprint `lem-weil-coefficient-frobenius`, at the separably closed point: for a separably
closed field `k` and `K ∈ Dctf(Spec k, Λ)`, the double-dual morphism `K ⟶ 𝔻 𝔻 K` of the point
`Spec k` over itself is an isomorphism: under `RΓ(Spec k, -)` it is derived evaluation into the
coefficient double dual of a perfect complex of `Λ`-modules. -/
theorem isIso_verdierDualDoubleDual_app_id_of_isSepClosed {k : Type u} [Field k] [IsSepClosed k]
    {K : _root_.DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) (Spec (.of k)) K) :
    IsIso ((verdierDualDoubleDual (ModuleCat.{u + 1} Λ) (𝟙 (Spec (.of k)))).app K) :=
  sorry

/-- **Detection on closed points and global sections.** Let `X` be of finite type over an
algebraically closed field `k`, with structure morphism `a`, and let `f : K ⟶ L` be a morphism
of bounded constructible complexes on `X_ét` whose geometric stalks are isomorphisms at every
nonclosed point. Then the cone of `f` is supported on finitely many closed points, and `f` is an
isomorphism as soon as `Ra_* f` is. -/
theorem isIso_of_isIso_rightDerivedLowerStar_map_of_not_isClosed {k : Type u} [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) [LocallyOfFiniteType a]
    [QuasiCompact a]
    {K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hL : boundedConstructible (ModuleCat.{u + 1} Λ) X L) (f : K ⟶ L)
    (hf : ∀ (x : X), ¬ IsClosed ({x} : Set X) → ∀ q : ℤ,
      IsIso ((X.uliftPointSmallEtale x).sheafFiber.map
        ((_root_.DerivedCategory.homologyFunctor _ q).map f)))
    (ha : IsIso ((R((a)_*[ModuleCat.{u + 1} Λ])).map f)) :
    IsIso f :=
  sorry

/-- **Compactification without raising the dimension.** An affine scheme `X` of finite type
over a field `k` with `dim X ≤ d` is a quasi-compact open subscheme of a proper `k`-scheme `Y`
with `dim Y ≤ d` (the scheme-theoretic closure of `X` in a Nagata compactification). -/
theorem exists_isProper_isOpenImmersion_topologicalKrullDim_le {k : Type u} [Field k]
    {X : Scheme.{u}} [IsAffine X] (a : X ⟶ Spec (.of k)) [LocallyOfFiniteType a] (d : ℕ)
    (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) :
    ∃ (Y : Scheme.{u}) (b : Y ⟶ Spec (.of k)) (j : X ⟶ Y), IsProper b ∧ IsOpenImmersion j ∧
      QuasiCompact j ∧ j ≫ b = a ∧ topologicalKrullDim Y ≤ (d : WithBot ℕ∞) :=
  sorry

/-- The statement proved by induction on the dimension: Verdier biduality on `Dctf(X, Λ)` for
every separated scheme `X` of finite type and of dimension at most `d` over an algebraically
closed field whose characteristic is invertible in `Λ`... -/
def BidualityUpTo (d : ℕ) : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] [HasInvertibleExponent Λ (Spec (.of k))]
    (X : Scheme.{u}) (a : X ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a]
    [QuasiCompact a], topologicalKrullDim X ≤ (d : WithBot ℕ∞) →
    ∀ (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        IsIso ((verdierDualDoubleDual (ModuleCat.{u + 1} Λ) a).app K)

/-- **Biduality at nonclosed points.** Assume Verdier biduality in dimensions `< d`. Let `X` be
separated of finite type over an algebraically closed field `k` with `dim X ≤ d`, and let
`K ∈ Dctf(X, Λ)`. Then at every nonclosed point `x` of `X` the geometric stalks of the
cohomology of `δ_K` are isomorphisms. A coordinate `t` on an affine neighbourhood `V` of `x`
sends `x` to the generic point of `𝔸¹_k`; the geometric generic fibre `V_η̄` has dimension
`< d` (`lem-fin-coordinate-generic-dimension`), so `δ` is an isomorphism on it, and it is the
restriction of `δ_K` (`lem-weil-geometric-generic-duality`, `lem-weil-delta-restriction`); and a
geometric point over `x` factors through `V_η̄`. -/
theorem isIso_sheafFiber_map_verdierDualDoubleDual_app_of_not_isClosed (d : ℕ)
    (IH : ∀ d' < d, BidualityUpTo Λ d') {k : Type u} [Field k] [IsAlgClosed k]
    [HasInvertibleExponent Λ (Spec (.of k))] {X : Scheme.{u}} (a : X ⟶ Spec (.of k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) (x : X)
    (hx : ¬ IsClosed ({x} : Set X)) (q : ℤ) :
    IsIso ((X.uliftPointSmallEtale x).sheafFiber.map
      ((_root_.DerivedCategory.homologyFunctor _ q).map
        ((verdierDualDoubleDual (ModuleCat.{u + 1} Λ) a).app K))) :=
  sorry

end Steps

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
