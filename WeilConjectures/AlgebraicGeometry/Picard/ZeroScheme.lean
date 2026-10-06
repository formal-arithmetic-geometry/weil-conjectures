/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
public import WeilConjectures.AlgebraicGeometry.Hilbert.Defs
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.AlgebraicGeometry.Picard.Representability
public import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier

/-!
# The zero-scheme dictionary and the representability of `F`

Let `k` be a separably closed field, let `X` be a smooth proper geometrically integral curve
over `k` of genus `g` and let `σ` be a `k`-rational point of `X`.  Write `F` for the subfunctor
`AlgebraicGeometry.picardFunctorInvertibleDirectImage` of the `σ`-normalized Picard functor,
cut out by the condition that `Rf_{T,*} ℒ` is an invertible `𝒪_T`-module placed in degree `0`.

This file states the last three steps of the representability of `F`:

* the *zero-scheme dictionary*: a class `ℒ ∈ F(T)` gives rise to a relative effective Cartier
  divisor `D = Z(s) ⊆ X_T`, finite locally free of degree `g` over `T`, where `s` is the
  section of `ℒ ⊗ f_T^* 𝒩^{-1}` adjoint to an isomorphism `Rf_{T,*} ℒ ≅ 𝒩[0]`;
* the resulting injection `F ↪ Hilb^g_{X/k}` of functors;
* the representability of `F` by an open subscheme of `Hilb^g_{X/k}`.

## Implementation notes

The divisor is the zero scheme `Z(φ)` (`AlgebraicGeometry.Scheme.Modules.Hom.zeroLocus`) of the
adjunction morphism `φ : f_T^* f_{T,*} ℒ ⟶ ℒ`
(`AlgebraicGeometry.Scheme.Pic.directImageCounit`). For `ℒ ∈ F(T)` the module
`𝒩 = f_{T,*} ℒ ≅ R⁰f_{T,*} ℒ` is invertible, and `Z(φ)` is the zero scheme `Z(s)` of the section
`s ∈ H⁰(X_T, ℒ ⊗ f_T^* 𝒩^{-1})` adjoint to `Rf_{T,*} ℒ ≅ 𝒩[0]` in the blueprint: both are cut
out locally by the coefficient of `φ` in local trivializations. The morphism is used instead of
the section because the tensor-hom identification `Hom(f_T^* 𝒩, ℒ) ≅ H⁰(ℒ ⊗ f_T^* 𝒩^{-1})` is
not available.

There is no definition of a *relative* effective Cartier divisor; the two conditions it
consists of, invertibility of the ideal and flatness over `T`, are used directly (see
`WeilConjectures/AlgebraicGeometry/RelativeEffectiveCartier`). The subsection statement keeps
its existential form: there is a point of the Hilbert functor `Hilb^g_{X/k}(T)` whose closed
subscheme is an effective Cartier centre in `X_T`, the witness being `Z(φ)`.

Since `AlgebraicGeometry.picardPresheaf` is `Type (u + 1)`-valued while
`AlgebraicGeometry.hilbertPresheaf` is `Type u`-valued, the natural transformation `F ↪ Hilb^g`
is stated after composing the Hilbert functor with `CategoryTheory.uliftFunctor.{u + 1, u}`,
which changes nothing since that functor is fully faithful; this is the same device as the
`CategoryTheory.uliftYoneda` of `WeilConjectures/AlgebraicGeometry/Picard/Representability`.

The structure morphism `X ⟶ Spec k` is carried as an `AlgebraicGeometry.Scheme.Over` instance
and written `X ↘ Spec (.of k)`, as in `WeilConjectures/AlgebraicGeometry/Curve/RiemannRoch`,
because `AlgebraicGeometry.Scheme.arithmeticGenus` needs that instance.

The instance hypothesis `∀ T, HasInjectiveResolutions (X ×[k] T).Modules` is the one nothing
can discharge yet; see `AlgebraicGeometry.Scheme.Modules.isGrothendieckAbelian`.

## Main definitions

- `AlgebraicGeometry.Scheme.Pic.directImageCounit`: the adjunction morphism
  `f_T^* f_{T,*} ℒ ⟶ ℒ`.

## Main statements

- `AlgebraicGeometry.isInvertible_zeroLocus_directImageCounit`: the zero scheme of the adjunction
  morphism is a relative effective Cartier divisor, finite locally free of degree `g` (blueprint
  `lem-pc-zero-scheme-recd`).
- `AlgebraicGeometry.exists_isEffectiveCartierCenter_hilbertPresheaf`: the zero-scheme
  dictionary (blueprint `sk-lem-picard-zero-dictionary`).
- `AlgebraicGeometry.comap_zeroLocus_directImageCounit`: the dictionary is natural in `T`.
- `AlgebraicGeometry.eq_of_zeroLocus_directImageCounit_eq`: the dictionary is injective.
- `AlgebraicGeometry.exists_injective_natTrans_hilbertPresheaf`: `F` is a subfunctor of the
  Hilbert functor (blueprint
  `sk-the-subsheaf-ff-and-its-representability--remark-1`).
- `AlgebraicGeometry.isRepresentable_picardFunctorInvertibleDirectImage`: `F` is representable
  by an open subscheme of `Hilb^g_{X/k}` (blueprint `sk-thm-picard-f-representable`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

open Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  [GeometricallyIntegral (X ↘ Spec (.of k))]

/-- For a class `ℒ ∈ Pic(X_T)`, the adjunction morphism `f_T^* f_{T,*} ℒ ⟶ ℒ`, where
`f_T : X_T ⟶ T` is the base change of `f`. For `ℒ ∈ F(T)` the module `𝒩 = f_{T,*} ℒ` is
invertible with `Rf_{T,*} ℒ ≅ 𝒩[0]`, and this is the morphism whose zero scheme is the divisor
of the zero-scheme dictionary. -/
noncomputable def Scheme.Pic.directImageCounit {S : Scheme.{u}} (f : X ⟶ S) (T : Over S)
    (L : (Limits.pullback f T.hom).Pic) :
    (Modules.pullback (Limits.pullback.snd f T.hom)).obj
        ((Modules.pushforward (Limits.pullback.snd f T.hom)).obj
          ((fromSkeleton _).obj L.val)) ⟶ (fromSkeleton _).obj L.val :=
  (Modules.pullbackPushforwardAdjunction _).counit.app _

/-- **The fibres of the adjunction section are nonzero.** For `ℒ ∈ F(T)` and a point `t` of `T`,
the zero scheme of the adjunction morphism `φ : f_T^* f_{T,*} ℒ ⟶ ℒ` does not contain the
fibre `X_t`: the restriction of its ideal to `X_t` is nonzero.

This is the step `s_t ≠ 0` of the blueprint proof of `lem-pc-zero-scheme-recd`: by cohomology
and base change, `Rf_{t,*} ℒ_t ≅ 𝒩_t[0]` with `𝒩_t ≅ κ(t)`, and the base change `φ_t` of `φ`
is the adjunction morphism of `ℒ_t`, which corresponds to the identity of `𝒩_t` and is
therefore nonzero; then `Z(φ)|_{X_t} = Z(φ_t) ≠ X_t`. -/
theorem comap_fiberι_zeroLocus_directImageCounit_ne_bot
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ X ↘ Spec (.of k) = 𝟙 (Spec (.of k)))
    [∀ T : Over (Spec (.of k)),
      HasInjectiveResolutions (Limits.pullback (X ↘ Spec (.of k)) T.hom).Modules]
    (T : Over (Spec (.of k)))
    (ℒ : (picardFunctorInvertibleDirectImage (X ↘ Spec (.of k)) σ hσ).toFunctor.obj (op T))
    (t : T.left) :
    (Pic.directImageCounit (X ↘ Spec (.of k)) T ℒ.1.1).zeroLocus.comap
      ((Limits.pullback.snd (X ↘ Spec (.of k)) T.hom).fiberι t) ≠ ⊥ :=
  sorry

/-- **The degree of the zero scheme of the adjunction section is the genus.** For `ℒ ∈ F(T)`,
the rank at every point `t` of `T` of the projection `Z(φ) ⟶ T` from the zero scheme of the
adjunction morphism `φ : f_T^* f_{T,*} ℒ ⟶ ℒ` is the genus `g` of `X`.

This is the degree computation of the blueprint proof of `lem-pc-zero-scheme-recd`: the rank
at `t` is `dim_{κ(t)} Γ(D_t, 𝒪_{D_t}) = deg D_t = deg 𝒪(D_t) = deg ℒ_t`, and
`deg ℒ_t = χ(ℒ_t) - χ(𝒪_{X_t}) = 1 - (1 - g) = g` by `AlgebraicGeometry.Scheme.degree_eq_genus`
(blueprint `sk-cor-picard-degree-g`), since `h⁰(ℒ_t) = 1` and the higher cohomology of `ℒ_t`
vanishes by cohomology and base change. -/
theorem finrank_zeroLocus_directImageCounit
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ X ↘ Spec (.of k) = 𝟙 (Spec (.of k)))
    [∀ T : Over (Spec (.of k)),
      HasInjectiveResolutions (Limits.pullback (X ↘ Spec (.of k)) T.hom).Modules]
    (T : Over (Spec (.of k)))
    (ℒ : (picardFunctorInvertibleDirectImage (X ↘ Spec (.of k)) σ hσ).toFunctor.obj (op T))
    (t : T.left) :
    ((Pic.directImageCounit (X ↘ Spec (.of k)) T ℒ.1.1).zeroLocus.subschemeι ≫
      Limits.pullback.snd (X ↘ Spec (.of k)) T.hom).finrank t = arithmeticGenus k X :=
  sorry

/-- **The zero scheme of the adjunction section.** Let `ℒ ∈ F(T)`, let `𝒩 = f_{T,*} ℒ`, so that
`Rf_{T,*} ℒ ≅ 𝒩[0]` with `𝒩` invertible, and let `φ : f_T^* 𝒩 ⟶ ℒ` be the adjunction morphism,
i.e. the section `s` of `ℒ ⊗ f_T^* 𝒩^{-1}` of the blueprint. Then the zero scheme
`D = Z(φ) ⊆ X_T` is a relative effective Cartier divisor on `X_T/T` (its ideal is invertible
and `D ⟶ T` is flat) which is finite locally free of degree `g` over `T`: it lies in the
Hilbert functor `Hilb^g_{X/k}(T)`.

(blueprint: `lem-pc-zero-scheme-recd`) -/
theorem isInvertible_zeroLocus_directImageCounit
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ X ↘ Spec (.of k) = 𝟙 (Spec (.of k)))
    [∀ T : Over (Spec (.of k)),
      HasInjectiveResolutions (Limits.pullback (X ↘ Spec (.of k)) T.hom).Modules]
    (T : Over (Spec (.of k)))
    (ℒ : (picardFunctorInvertibleDirectImage (X ↘ Spec (.of k)) σ hσ).toFunctor.obj (op T)) :
    (Pic.directImageCounit (X ↘ Spec (.of k)) T ℒ.1.1).zeroLocus.IsInvertible ∧
      IsHilbertSubscheme (X ↘ Spec (.of k)) (arithmeticGenus k X) T
        (Pic.directImageCounit (X ↘ Spec (.of k)) T ℒ.1.1).zeroLocus := by
  set π := Limits.pullback.snd (X ↘ Spec (.of k)) T.hom
  have := smoothOfRelativeDimension_isStableUnderBaseChange 1
  have : SmoothOfRelativeDimension 1 π :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ ‹_›
  -- `ℒ`, `𝒩 = f_{T,*} ℒ ≅ R⁰f_{T,*} ℒ` and `f_T^* 𝒩` are invertible.
  have hℒ := ℒ.1.1.isInvertible
  have h𝒩 : SheafOfModules.IsInvertible.{u, u, u}
      ((Modules.pushforward π).obj ((fromSkeleton _).obj ℒ.1.1.val)) :=
    have := ℒ.2.1
    SheafOfModules.IsInvertible.of_iso.{u, u, u}
      ((Functor.rightDerivedZeroIsoSelf (Modules.pushforward π)).app _)
  have := h𝒩.pullback (g := π)
  -- `D = Z(φ)` is locally principal, and its fibres are effective Cartier divisors on the
  -- integral fibres `X_t`.
  have hD := (Pic.directImageCounit (X ↘ Spec (.of k)) T ℒ.1.1).isLocallyPrincipal_zeroLocus
  have hfib (t : T.left) := (hD.comap (π.fiberι t)).isInvertible
    (comap_fiberι_zeroLocus_directImageCounit_ne_bot σ hσ T ℒ t)
  obtain ⟨hinv, hflat⟩ := hD.isInvertible_and_flat π hfib
  obtain ⟨hfin, hlfp⟩ := hinv.isFinite_and_locallyOfFinitePresentation π hflat
  exact ⟨hinv, hfin, hflat, hlfp, finrank_zeroLocus_directImageCounit σ hσ T ℒ⟩

/-- **The zero-scheme dictionary.** Let `ℒ ∈ F(T)`, let `𝒩` be the invertible `𝒪_T`-module with
`Rf_{T,*} ℒ ≅ 𝒩[0]` provided by the definition of `F`, and let
`s ∈ H⁰(X_T, ℒ ⊗ f_T^* 𝒩^{-1})` be the section adjoint to that isomorphism.  Then the zero
scheme `D = Z(s) ⊆ X_T` is a relative effective Cartier divisor on `X_T/T`, finite locally free
of degree `g` over `T`, where `g` is the genus of the curve.

There is no definition of a relative effective Cartier divisor, so the conclusion is stated
as the existence of the divisor: there is a point `D` of the Hilbert functor `Hilb^g_{X/k}(T)`
whose closed subscheme is moreover an effective Cartier centre in `X_T`.

The witness is the zero scheme of the adjunction morphism, by
`AlgebraicGeometry.isInvertible_zeroLocus_directImageCounit`.

(blueprint: `sk-lem-picard-zero-dictionary`) -/
theorem exists_isEffectiveCartierCenter_hilbertPresheaf [IsSepClosed k]
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ X ↘ Spec (.of k) = 𝟙 (Spec (.of k)))
    [∀ T : Over (Spec (.of k)),
      HasInjectiveResolutions (Limits.pullback (X ↘ Spec (.of k)) T.hom).Modules]
    (T : Over (Spec (.of k)))
    (ℒ : (picardFunctorInvertibleDirectImage (X ↘ Spec (.of k)) σ hσ).toFunctor.obj (op T)) :
    ∃ D : (hilbertPresheaf (X ↘ Spec (.of k)) (arithmeticGenus k X)).obj (op T),
      IsEffectiveCartierCenter D.1.subschemeι :=
  have h := isInvertible_zeroLocus_directImageCounit σ hσ T ℒ
  ⟨⟨_, h.2⟩, h.1.isEffectiveCartierCenter⟩

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  [GeometricallyIntegral (X ↘ Spec (.of k))] in
/-- For `ℒ ∈ F(T)`, the source `f_T^* f_{T,*} ℒ` of the adjunction morphism is invertible, since
`f_{T,*} ℒ ≅ R⁰f_{T,*} ℒ` is. -/
lemma isInvertible_pullback_pushforward
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ X ↘ Spec (.of k) = 𝟙 (Spec (.of k)))
    [∀ T : Over (Spec (.of k)),
      HasInjectiveResolutions (Limits.pullback (X ↘ Spec (.of k)) T.hom).Modules]
    (T : Over (Spec (.of k)))
    (ℒ : (picardFunctorInvertibleDirectImage (X ↘ Spec (.of k)) σ hσ).toFunctor.obj (op T)) :
    SheafOfModules.IsInvertible.{u, u, u}
      ((Modules.pullback (Limits.pullback.snd (X ↘ Spec (.of k)) T.hom)).obj
        ((Modules.pushforward (Limits.pullback.snd (X ↘ Spec (.of k)) T.hom)).obj
          ((fromSkeleton _).obj ℒ.1.1.val))) :=
  have := ℒ.2.1
  (SheafOfModules.IsInvertible.of_iso.{u, u, u}
    ((Functor.rightDerivedZeroIsoSelf (Modules.pushforward _)).app _)).pullback

/-- **The adjunction morphism commutes with base change.** For `ℒ ∈ F(T)` and a morphism
`i : T' ⟶ T` of `k`-schemes, with base change `i' : X_{T'} ⟶ X_T`, the pullback
`i'^* φ_ℒ : i'^* f_T^* f_{T,*} ℒ ⟶ i'^* ℒ` of the adjunction morphism of `ℒ` is isomorphic, as
an arrow, to the adjunction morphism `f_{T'}^* f_{T',*} ℒ_{T'} ⟶ ℒ_{T'}` of the pulled back class
`ℒ_{T'} = i'^* ℒ`.

This is cohomology and base change for `F`: since `Rf_{T,*} ℒ ≅ 𝒩[0]` with `𝒩` invertible, the
base change map `i^* f_{T,*} ℒ ⟶ f_{T',*} i'^* ℒ` is an isomorphism, and it is compatible with the
two adjunction morphisms by construction (it is the mate of `i'^* f_T^* ≅ f_{T'}^* i^*`). -/
theorem nonempty_arrowIso_pullback_directImageCounit
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ X ↘ Spec (.of k) = 𝟙 (Spec (.of k)))
    [∀ T : Over (Spec (.of k)),
      HasInjectiveResolutions (Limits.pullback (X ↘ Spec (.of k)) T.hom).Modules]
    {T T' : Over (Spec (.of k))} (i : T' ⟶ T)
    (ℒ : (picardFunctorInvertibleDirectImage (X ↘ Spec (.of k)) σ hσ).toFunctor.obj (op T)) :
    Nonempty (Arrow.mk ((Modules.pullback (baseChangeMap (X ↘ Spec (.of k)) i)).map
        (Pic.directImageCounit (X ↘ Spec (.of k)) T ℒ.1.1)) ≅
      Arrow.mk (Pic.directImageCounit (X ↘ Spec (.of k)) T'
        (Pic.map (baseChangeMap (X ↘ Spec (.of k)) i) ℒ.1.1))) :=
  sorry

/-- **The zero-scheme dictionary is natural.** For `ℒ ∈ F(T)` and `i : T' ⟶ T`, the zero scheme
of the adjunction morphism of `ℒ_{T'}` is the base change to `X_{T'}` of the zero scheme of the
adjunction morphism of `ℒ`: `Z(φ_{ℒ_{T'}}) = Z(φ_ℒ) ×_{X_T} X_{T'}`. -/
theorem comap_zeroLocus_directImageCounit
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ X ↘ Spec (.of k) = 𝟙 (Spec (.of k)))
    [∀ T : Over (Spec (.of k)),
      HasInjectiveResolutions (Limits.pullback (X ↘ Spec (.of k)) T.hom).Modules]
    {T T' : Over (Spec (.of k))} (i : T' ⟶ T)
    (ℒ : (picardFunctorInvertibleDirectImage (X ↘ Spec (.of k)) σ hσ).toFunctor.obj (op T)) :
    (Pic.directImageCounit (X ↘ Spec (.of k)) T ℒ.1.1).zeroLocus.comap
        (baseChangeMap (X ↘ Spec (.of k)) i) =
      (Pic.directImageCounit (X ↘ Spec (.of k)) T'
        (Pic.map (baseChangeMap (X ↘ Spec (.of k)) i) ℒ.1.1)).zeroLocus := by
  have := ℒ.1.1.isInvertible
  have := isInvertible_pullback_pushforward σ hσ T ℒ
  rw [Modules.Hom.comap_zeroLocus]
  exact Modules.Hom.zeroLocus_eq_of_arrowIso _ _
    (nonempty_arrowIso_pullback_directImageCounit σ hσ i ℒ).some

/-- **The zero-scheme dictionary is injective.** Two classes `ℒ, ℒ' ∈ F(T)` whose adjunction
morphisms have the same zero scheme `D` are equal.

Writing `𝒩 = f_{T,*} ℒ` and `𝒩' = f_{T,*} ℒ'`, both `ℒ ≅ 𝒪(D) ⊗ f_T^* 𝒩` and
`ℒ' ≅ 𝒪(D) ⊗ f_T^* 𝒩'`
(`AlgebraicGeometry.Scheme.Modules.Hom.nonempty_iso_dual_toModules_tensorObj`).
Pulling back along the section `σ_T`, along which both classes are trivial, gives
`𝒪_T ≅ σ_T^* 𝒪(D) ⊗ 𝒩` and `𝒪_T ≅ σ_T^* 𝒪(D) ⊗ 𝒩'`, hence `𝒩 ≅ 𝒩'` and `ℒ ≅ ℒ'`: this is the
inverse `D ↦ 𝒪(D) ⊗ pr_T^* σ_T^* 𝒪(D)^{-1}` of the blueprint. -/
theorem eq_of_zeroLocus_directImageCounit_eq
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ X ↘ Spec (.of k) = 𝟙 (Spec (.of k)))
    [∀ T : Over (Spec (.of k)),
      HasInjectiveResolutions (Limits.pullback (X ↘ Spec (.of k)) T.hom).Modules]
    (T : Over (Spec (.of k)))
    (ℒ ℒ' : (picardFunctorInvertibleDirectImage (X ↘ Spec (.of k)) σ hσ).toFunctor.obj (op T))
    (h : (Pic.directImageCounit (X ↘ Spec (.of k)) T ℒ.1.1).zeroLocus =
      (Pic.directImageCounit (X ↘ Spec (.of k)) T ℒ'.1.1).zeroLocus) :
    ℒ = ℒ' := by
  set π := Limits.pullback.snd (X ↘ Spec (.of k)) T.hom
  set D := (Pic.directImageCounit (X ↘ Spec (.of k)) T ℒ.1.1).zeroLocus
  -- Each class `ℳ ∈ F(T)` with zero scheme `D` is `𝒪(D) ⊗ f_T^* 𝒩` with
  -- `𝒪_T ≅ σ_T^* 𝒪(D) ⊗ 𝒩`, for `𝒩 = f_{T,*} ℳ`.
  have key (ℳ : (picardFunctorInvertibleDirectImage (X ↘ Spec (.of k)) σ hσ).toFunctor.obj
      (op T)) (hℳ : (Pic.directImageCounit (X ↘ Spec (.of k)) T ℳ.1.1).zeroLocus = D) :
      ∃ 𝒩 : T.left.Modules,
        Nonempty ((fromSkeleton _).obj ℳ.1.1.val ≅ D.toModulesᵛ ⊗ (Modules.pullback π).obj 𝒩) ∧
        Nonempty (𝟙_ T.left.Modules ≅
          (Modules.pullback (sectionBaseChange _ σ hσ T)).obj D.toModulesᵛ ⊗ 𝒩) := by
    have := ℳ.1.1.isInvertible
    have := isInvertible_pullback_pushforward σ hσ T ℳ
    have hinv := (isInvertible_zeroLocus_directImageCounit σ hσ T ℳ).1
    obtain ⟨e⟩ := Modules.Hom.nonempty_iso_dual_toModules_tensorObj _ hinv
    rw [hℳ] at e
    refine ⟨_, ⟨e⟩, ?_⟩
    obtain ⟨n⟩ : Nonempty ((Modules.pullback (sectionBaseChange _ σ hσ T)).obj
        ((fromSkeleton _).obj ℳ.1.1.val) ≅ SheafOfModules.unit _) :=
      toSkeleton_eq_toSkeleton_iff.mp (congrArg Pic.val ℳ.1.2)
    obtain ⟨t⟩ := Modules.nonempty_pullback_tensorObj_iso (sectionBaseChange _ σ hσ T) D.toModulesᵛ
      ((Modules.pullback π).obj ((Modules.pushforward π).obj ((fromSkeleton _).obj ℳ.1.1.val)))
    exact ⟨n.symm ≪≫ (Modules.pullback _).mapIso e ≪≫ t ≪≫ whiskerLeftIso _
      ((Modules.pullbackComp _ π).app _ ≪≫
        (Modules.pullbackCongr (sectionBaseChange_snd _ σ hσ T)).app _ ≪≫
        (Modules.pullbackId _).app _)⟩
  obtain ⟨𝒩, ⟨e⟩, ⟨n⟩⟩ := key ℒ rfl
  obtain ⟨𝒩', ⟨e'⟩, ⟨n'⟩⟩ := key ℒ' h.symm
  -- `𝒪_T ≅ A ⊗ 𝒩` and `𝒪_T ≅ A ⊗ 𝒩'` give `𝒩 ≅ 𝒩'`.
  let i : 𝒩 ≅ 𝒩' := (λ_ 𝒩).symm ≪≫ whiskerRightIso n' 𝒩 ≪≫ whiskerRightIso (β_ _ 𝒩') 𝒩 ≪≫
    α_ 𝒩' _ 𝒩 ≪≫ whiskerLeftIso 𝒩' n.symm ≪≫ ρ_ 𝒩'
  have hval : ℒ.1.1.val = ℒ'.1.1.val := by
    rw [← toSkeleton_fromSkeleton_obj ℒ.1.1.val, ← toSkeleton_fromSkeleton_obj ℒ'.1.1.val]
    exact congr_toSkeleton_of_iso
      (e ≪≫ whiskerLeftIso D.toModulesᵛ ((Modules.pullback π).mapIso i) ≪≫ e'.symm)
  exact Subtype.ext (Subtype.ext (Pic.ext hval))

/-- **`F` is a subfunctor of the Hilbert functor.** The dictionary `ℒ ↦ D = Z(s)` of
`AlgebraicGeometry.exists_isEffectiveCartierCenter_hilbertPresheaf` is natural in `T` and
injective, so it exhibits `F` as a subfunctor of `Hilb^g_{X/k}`; the inverse on the image is
`D ↦ 𝒪(D) ⊗ σ_T^* 𝒪(D)^{-1}`.  It is through this injection that the open subscheme
`W ⊆ Hilb^g_{X/k}` of
`AlgebraicGeometry.isRepresentable_picardFunctorInvertibleDirectImage` represents `F`.

`F` takes values in `Type (u + 1)` and `Hilb^g_{X/k}` in `Type u`, so the target is composed
with `CategoryTheory.uliftFunctor.{u + 1, u}`; being fully faithful, this changes neither the
functor nor the injectivity of the components.

The natural transformation sends `ℒ` to the zero scheme of its adjunction morphism
(`AlgebraicGeometry.isInvertible_zeroLocus_directImageCounit`); it is natural by
`AlgebraicGeometry.comap_zeroLocus_directImageCounit` and injective by
`AlgebraicGeometry.eq_of_zeroLocus_directImageCounit_eq`.

(blueprint: `sk-the-subsheaf-ff-and-its-representability--remark-1`) -/
theorem exists_injective_natTrans_hilbertPresheaf [IsSepClosed k]
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ X ↘ Spec (.of k) = 𝟙 (Spec (.of k)))
    [∀ T : Over (Spec (.of k)),
      HasInjectiveResolutions (Limits.pullback (X ↘ Spec (.of k)) T.hom).Modules] :
    ∃ Φ : (picardFunctorInvertibleDirectImage (X ↘ Spec (.of k)) σ hσ).toFunctor ⟶
      hilbertPresheaf (X ↘ Spec (.of k)) (arithmeticGenus k X) ⋙ uliftFunctor.{u + 1, u},
      ∀ T, Function.Injective (Φ.app T) := by
  refine ⟨{
    app T := TypeCat.ofHom fun ℒ ↦ ULift.up
      ⟨_, (isInvertible_zeroLocus_directImageCounit σ hσ T.unop ℒ).2⟩
    naturality T T' i := ?_ }, fun T ℒ ℒ' h ↦ ?_⟩
  · ext ℒ
    exact ULift.ext _ _ (Subtype.ext (comap_zeroLocus_directImageCounit σ hσ i.unop ℒ).symm)
  · exact eq_of_zeroLocus_directImageCounit_eq σ hσ T.unop ℒ ℒ'
      congr($(congrArg ULift.down h).1)

/-- **`F` is representable** by an open subscheme of `Hilb^g_{X/k}`: given a `k`-scheme `H`
representing `Hilb^g_{X/k}`, there are a scheme `W` and an open immersion `j : W ⟶ H` such that
`W`, viewed as a `k`-scheme through `j`, represents `F`.

(blueprint: `sk-thm-picard-f-representable`) -/
theorem isRepresentable_picardFunctorInvertibleDirectImage [IsSepClosed k]
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ X ↘ Spec (.of k) = 𝟙 (Spec (.of k)))
    [∀ T : Over (Spec (.of k)),
      HasInjectiveResolutions (Limits.pullback (X ↘ Spec (.of k)) T.hom).Modules]
    (H : Over (Spec (.of k)))
    (e : (hilbertPresheaf (X ↘ Spec (.of k)) (arithmeticGenus k X)).RepresentableBy H) :
    ∃ (W : Scheme.{u}) (j : W ⟶ H.left), IsOpenImmersion j ∧
      Nonempty ((picardFunctorInvertibleDirectImage (X ↘ Spec (.of k)) σ hσ).toFunctor
        |>.RepresentableBy (Over.mk (j ≫ H.hom))) :=
  sorry

end AlgebraicGeometry
