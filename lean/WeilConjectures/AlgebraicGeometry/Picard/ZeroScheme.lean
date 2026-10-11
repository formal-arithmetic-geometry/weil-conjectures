/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
public import WeilConjectures.AlgebraicGeometry.Hilbert.Curve
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

- `AlgebraicGeometry.comap_fiberι_zeroLocus_directImageCounit_ne_bot`: the adjunction section is
  nonzero on every fibre `X_t`.
- `AlgebraicGeometry.finrank_zeroLocus_directImageCounit`: its zero scheme has degree `g` over
  `T`.
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
- `AlgebraicGeometry.zeroLocus_directImageCounit_eq_of_iso`: for `ℒ ≅ 𝒪(D) ⊗ f_T^* 𝒩` in `F(T)`
  the dictionary returns `D` (blueprint `lem-pc-universal-adjoint-section`).
- `AlgebraicGeometry.isRepresentable_picardFunctorInvertibleDirectImage`: `F` is representable
  by an open subscheme of `Hilb^g_{X/k}` (blueprint `sk-thm-picard-f-representable`,
  `thm-pc-f-representable`).
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

/-- A morphism smooth of relative dimension `1` is smooth, hence flat and locally of finite
presentation, as `AlgebraicGeometry.picardFunctorInvertibleDirectImage` requires. -/
local instance {Y Z : Scheme.{u}} (f : Y ⟶ Z) [SmoothOfRelativeDimension 1 f] : Smooth f :=
  SmoothOfRelativeDimension.smooth 1 f

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

/-- For a class `ℒ ∈ Pic(X_T)` over a nonempty `T` whose direct image `f_{T,*} ℒ` is invertible,
the adjunction morphism `f_T^* f_{T,*} ℒ ⟶ ℒ` is nonzero: by the triangle identity its adjoint is
the identity of `f_{T,*} ℒ`, which is nonzero. -/
theorem Scheme.Pic.directImageCounit_ne_zero {S : Scheme.{u}} (f : X ⟶ S) (T : Over S)
    [Nonempty T.left] (L : (Limits.pullback f T.hom).Pic)
    [SheafOfModules.IsInvertible.{u, u, u} ((Modules.pushforward (Limits.pullback.snd f T.hom)).obj
      ((fromSkeleton _).obj L.val))] :
    Pic.directImageCounit f T L ≠ 0 := by
  intro h0
  have tri := (Modules.pullbackPushforwardAdjunction
    (Limits.pullback.snd f T.hom)).right_triangle_components ((fromSkeleton _).obj L.val)
  change _ ≫ (Modules.pushforward _).map (Pic.directImageCounit f T L) = _ at tri
  rw [h0, Functor.map_zero, comp_zero] at tri
  have := Modules.IsInvertible.of_sheafOfModules
    ((Modules.pushforward (Limits.pullback.snd f T.hom)).obj ((fromSkeleton _).obj L.val))
  exact Modules.IsInvertible.not_isZero _ ((IsZero.iff_id_eq_zero _).mpr tri.symm)

omit [GeometricallyIntegral (X ↘ Spec (.of k))] in
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

/-- **The fibres of the adjunction section are nonzero.** For `ℒ ∈ F(T)` and a point `t` of `T`,
the zero scheme of the adjunction morphism `φ : f_T^* f_{T,*} ℒ ⟶ ℒ` does not contain the
fibre `X_t`: the restriction of its ideal to `X_t` is nonzero.

This is the step `s_t ≠ 0` of the blueprint proof of `lem-pc-zero-scheme-recd`: by cohomology
and base change, `ℒ_t` lies in `F(κ(t))`, so `𝒩_t = f_{t,*} ℒ_t` is invertible, and the base
change `φ_t` of `φ` is the adjunction morphism of `ℒ_t`
(`AlgebraicGeometry.comap_zeroLocus_directImageCounit`), whose adjoint is the identity of the
nonzero module `𝒩_t` (`AlgebraicGeometry.Scheme.Pic.directImageCounit_ne_zero`); hence
`Z(φ)|_{X_t} = Z(φ_t) ≠ X_t` (`lem-pc-zero-scheme-properties` (3)). -/
theorem comap_fiberι_zeroLocus_directImageCounit_ne_bot
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ X ↘ Spec (.of k) = 𝟙 (Spec (.of k)))
    [∀ T : Over (Spec (.of k)),
      HasInjectiveResolutions (Limits.pullback (X ↘ Spec (.of k)) T.hom).Modules]
    (T : Over (Spec (.of k)))
    (ℒ : (picardFunctorInvertibleDirectImage (X ↘ Spec (.of k)) σ hσ).toFunctor.obj (op T))
    (t : T.left) :
    (Pic.directImageCounit (X ↘ Spec (.of k)) T ℒ.1.1).zeroLocus.comap
      ((Limits.pullback.snd (X ↘ Spec (.of k)) T.hom).fiberι t) ≠ ⊥ := by
  -- pass to the point `T' = Spec κ(t)` of `T`
  let T' : Over (Spec (.of k)) := Over.mk (T.left.fromSpecResidueField t ≫ T.hom)
  let i : T' ⟶ T := Over.homMk (T.left.fromSpecResidueField t)
  let L' := Pic.map (baseChangeMap (X ↘ Spec (.of k)) i) ℒ.1.1
  have hL' := IsInvertibleDirectImage.map_of_isProper (X ↘ Spec (.of k)) i ℒ.2
  have h𝒩 : SheafOfModules.IsInvertible.{u, u, u}
      ((Modules.pushforward (Limits.pullback.snd (X ↘ Spec (.of k)) T'.hom)).obj
        ((fromSkeleton _).obj L'.val)) :=
    have := hL'.1
    SheafOfModules.IsInvertible.of_iso.{u, u, u}
      ((Functor.rightDerivedZeroIsoSelf (Modules.pushforward _)).app _)
  have := h𝒩.pullback (g := Limits.pullback.snd (X ↘ Spec (.of k)) T'.hom)
  have := L'.isInvertible
  have : Nonempty T'.left :=
    ⟨(IsLocalRing.closedPoint (T.left.residueField t) : Spec (T.left.residueField t))⟩
  have hne : (Pic.directImageCounit (X ↘ Spec (.of k)) T' L').zeroLocus ≠ ⊥ := by
    rw [Ne, Modules.Hom.zeroLocus_eq_bot_iff]
    exact Pic.directImageCounit_ne_zero (X ↘ Spec (.of k)) T' L'
  -- the fibre `X_t` is the base change `X_{T'}`
  let e : (Limits.pullback.snd (X ↘ Spec (.of k)) T.hom).fiber t ≅
      Limits.pullback (X ↘ Spec (.of k)) T'.hom :=
    pullbackLeftPullbackSndIso (X ↘ Spec (.of k)) T.hom (T.left.fromSpecResidueField t)
  have he : e.hom ≫ baseChangeMap (X ↘ Spec (.of k)) i =
      (Limits.pullback.snd (X ↘ Spec (.of k)) T.hom).fiberι t := by
    apply Limits.pullback.hom_ext
    · simp only [Category.assoc, Limits.pullback.lift_fst, Category.comp_id]
      exact pullbackLeftPullbackSndIso_hom_fst _ _ _
    · simp [e, Scheme.Hom.fiberι, i, T', Limits.pullback.condition]
  intro hbot
  apply hne
  have h' : ((Pic.directImageCounit (X ↘ Spec (.of k)) T ℒ.1.1).zeroLocus.comap
      (baseChangeMap (X ↘ Spec (.of k)) i)).comap e.hom = ⊥ := by
    rw [← IdealSheafData.comap_comp, he, hbot]
  rw [← comap_zeroLocus_directImageCounit σ hσ i ℒ, ← IdealSheafData.comap_id
    (IdealSheafData.comap _ _), ← e.inv_hom_id, IdealSheafData.comap_comp, h',
    IdealSheafData.comap_bot]

/-- **The zero scheme of the adjunction section is a relative divisor.** For `ℒ ∈ F(T)`, the zero
scheme `D = Z(φ) ⊆ X_T` of the adjunction morphism `φ : f_T^* f_{T,*} ℒ ⟶ ℒ` is an effective
Cartier divisor which is finite locally free over `T`.

This is the first half of the blueprint proof of `lem-pc-zero-scheme-recd`: `D` is locally
principal, its fibres `D_t` are effective Cartier divisors on the integral curves `X_t` since
`φ_t ≠ 0`, so `D` is a relative effective Cartier divisor (`lem-pc-recd-locally-principal`), and
the Cartier criterion (`lem-pc-cartier-criterion`) makes it finite locally free over `T`. -/
theorem isInvertible_zeroLocus_directImageCounit_and_isFiniteLocallyFree
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ X ↘ Spec (.of k) = 𝟙 (Spec (.of k)))
    [∀ T : Over (Spec (.of k)),
      HasInjectiveResolutions (Limits.pullback (X ↘ Spec (.of k)) T.hom).Modules]
    (T : Over (Spec (.of k)))
    (ℒ : (picardFunctorInvertibleDirectImage (X ↘ Spec (.of k)) σ hσ).toFunctor.obj (op T)) :
    (Pic.directImageCounit (X ↘ Spec (.of k)) T ℒ.1.1).zeroLocus.IsInvertible ∧
      ((Pic.directImageCounit (X ↘ Spec (.of k)) T ℒ.1.1).zeroLocus.subschemeι ≫
        Limits.pullback.snd (X ↘ Spec (.of k)) T.hom).IsFiniteLocallyFree := by
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
  exact ⟨hinv, { toIsFinite := hfin, toFlat := hflat, toLocallyOfFinitePresentation := hlfp }⟩

/-- **The degree of the zero scheme of the adjunction section is the genus.** For `ℒ ∈ F(T)`,
the rank at every point `t` of `T` of the projection `Z(φ) ⟶ T` from the zero scheme of the
adjunction morphism `φ : f_T^* f_{T,*} ℒ ⟶ ℒ` is the genus `g` of `X`.

This is the degree computation of the blueprint proof of `lem-pc-zero-scheme-recd`: the rank
at `t` is `dim_{κ(t)} Γ(D_t, 𝒪_{D_t}) = deg D_t = deg 𝒪(D_t)`, and `ℒ_t ≅ 𝒪(D_t) ⊗ f_t^* 𝒩_t`
with `f_t^* 𝒩_t` pulled back from the point `Spec κ(t)`, hence of degree `0`. Finally
`deg ℒ_t = χ(ℒ_t) - χ(𝒪_{X_t}) = 1 - (1 - g) = g` as in `sk-cor-picard-degree-g`: the fibre
cohomology of `ℒ ∈ F(T)` is `h⁰(ℒ_t) = 1`, `h^q(ℒ_t) = 0` for `q > 0` (cohomology and base
change, `Modules.range_subset_setOf_hFiber_eq_iff`), and `χ(𝒪_{X_t}) = χ(𝒪_X) = 1 - g` by
invariance of the fibre Euler characteristic under base change and Riemann–Roch. -/
theorem finrank_zeroLocus_directImageCounit
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ X ↘ Spec (.of k) = 𝟙 (Spec (.of k)))
    [∀ T : Over (Spec (.of k)),
      HasInjectiveResolutions (Limits.pullback (X ↘ Spec (.of k)) T.hom).Modules]
    (T : Over (Spec (.of k)))
    (ℒ : (picardFunctorInvertibleDirectImage (X ↘ Spec (.of k)) σ hσ).toFunctor.obj (op T))
    (t : T.left) :
    ((Pic.directImageCounit (X ↘ Spec (.of k)) T ℒ.1.1).zeroLocus.subschemeι ≫
      Limits.pullback.snd (X ↘ Spec (.of k)) T.hom).finrank t = arithmeticGenus k X := by
  have := (isInvertible_zeroLocus_directImageCounit_and_isFiniteLocallyFree σ hσ T ℒ).2
  let π := Limits.pullback.snd (X ↘ Spec (.of k)) T.hom
  let φ := Pic.directImageCounit (X ↘ Spec (.of k)) T ℒ.1.1
  let D := φ.zeroLocus
  let ℳ := (fromSkeleton _).obj ℒ.1.1.val
  let 𝒩 := (Modules.pushforward π).obj ℳ
  let ι := π.fiberι t
  let κ := T.left.residueField t
  let _ := π.fiberOverSpecResidueField t
  change (D.subschemeι ≫ π).finrank t = _
  have := smoothOfRelativeDimension_isStableUnderBaseChange 1
  have : SmoothOfRelativeDimension 1 π :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ ‹_›
  have : IsProper π := MorphismProperty.pullback_snd (P := @IsProper) _ _ ‹_›
  have : SmoothOfRelativeDimension 1 (π.fiber t ↘ Spec κ) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ ‹_›
  have : IsProper (π.fiber t ↘ Spec κ) :=
    MorphismProperty.pullback_snd (P := @IsProper) _ _ ‹_›
  -- invertibility of the modules involved
  have hℳ := ℒ.1.1.isInvertible
  have h𝒩 : SheafOfModules.IsInvertible.{u, u, u} 𝒩 :=
    have := ℒ.2.1
    SheafOfModules.IsInvertible.of_iso.{u, u, u}
      ((Functor.rightDerivedZeroIsoSelf (Modules.pushforward π)).app _)
  have : SheafOfModules.IsInvertible.{u, u, u} ((Modules.pullback π).obj 𝒩) := .pullback ‹_›
  -- the fibre `D_t` is an effective Cartier divisor on `X_t`
  have hDt : (D.comap ι).IsInvertible :=
    (φ.isLocallyPrincipal_zeroLocus.comap ι).isInvertible
      (comap_fiberι_zeroLocus_directImageCounit_ne_bot σ hσ T ℒ t)
  -- Step 1: the rank at `t` is `deg D_t = dim_{κ(t)} Γ(D_t, 𝒪)`
  have h1 : (D.subschemeι ≫ π).finrank t =
      ((D.comap ι).subschemeι ≫ π.fiber t ↘ Spec κ).finrankΓ := by
    rw [Scheme.Hom.finrank_eq_fiberDegree]
    refine Scheme.Hom.finrankΓ_eq_of_iso _ _
      ((pullbackRightPullbackFstIso π (T.left.fromSpecResidueField t) D.subschemeι).symm ≪≫
        pullbackSymmetry _ _ ≪≫ (D.comapIso ι).symm) (Iso.refl _) ?_
    simp only [ι, Scheme.Hom.fiberι, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      IdealSheafData.comapIso_inv_subschemeι_assoc, pullbackSymmetry_hom_comp_fst_assoc,
      Iso.refl_hom, Spec.map_id]
    exact pullbackRightPullbackFstIso_inv_snd_snd π (T.left.fromSpecResidueField t) D.subschemeι
  -- Step 2: `deg D_t = deg 𝒪(D_t)`
  have h2 : ((D.comap ι).toModulesᵛ).degree κ =
      (((D.comap ι).subschemeι ≫ π.fiber t ↘ Spec κ).finrankΓ : ℤ) :=
    hDt.degree_dual_toModules
  -- Step 3: `ℳ_t ≅ 𝒪(D_t) ⊗ ι^* π^* 𝒩`, so `deg ℳ_t = deg D_t + deg (ι^* π^* 𝒩)`
  have : SheafOfModules.IsInvertible.{u, u, u} ((Modules.pullback ι).obj ℳ) := .pullback ‹_›
  have : SheafOfModules.IsInvertible.{u, u, u}
      ((Modules.pullback ι).obj ((Modules.pullback π).obj 𝒩)) := .pullback ‹_›
  have hz : ((Modules.pullback ι).map φ).zeroLocus = D.comap ι :=
    (Modules.Hom.comap_zeroLocus ι φ).symm
  obtain ⟨e⟩ := Modules.Hom.nonempty_iso_dual_toModules_tensorObj ((Modules.pullback ι).map φ)
    (hz ▸ hDt)
  rw [hz] at e
  have := hDt.isInvertible_dual_toModules
  have : Modules.IsInvertible ((Modules.pullback ι).obj ((Modules.pullback π).obj 𝒩)) :=
    Modules.IsInvertible.of_sheafOfModules _
  have h3 := Modules.degree_tensorObj (k := κ) ((D.comap ι).toModulesᵛ)
    ((Modules.pullback ι).obj ((Modules.pullback π).obj 𝒩))
  rw [← Modules.degree_congr κ e] at h3
  -- Step 4: `ι^* π^* 𝒩` is pulled back from the point `Spec κ(t)`, so it has degree `0`
  have h4 : ((Modules.pullback ι).obj ((Modules.pullback π).obj 𝒩)).degree κ = 0 := by
    have : Modules.IsInvertible 𝒩 := Modules.IsInvertible.of_sheafOfModules _
    obtain ⟨e'⟩ := Modules.IsInvertible.nonempty_iso_unit
      (IsLocalRing.closedPoint κ : Spec κ)
      ((Modules.pullback (T.left.fromSpecResidueField t)).obj 𝒩)
    exact (Modules.degree_congr κ ((Modules.pullbackComp ι π).app 𝒩 ≪≫
      (Modules.pullbackCongr (π.fiber_fac t)).app 𝒩 ≪≫
      ((Modules.pullbackComp _ _).app 𝒩).symm ≪≫ (Modules.pullback _).mapIso e' ≪≫
      Modules.pullbackObjUnitIso _)).trans (Modules.degree_unit κ)
  -- Step 5: `h⁰(ℳ_t) = 1` and `h^q(ℳ_t) = 0` for `q > 0`
  have : Flat π := inferInstance
  have hfib : (∀ q ≠ 0, ℳ.hFiber π q t = 0) ∧ ℳ.hFiber π 0 t = 1 :=
    (Modules.range_subset_setOf_hFiber_eq_iff π ℳ
      (Modules.isFlatOver_of_isInvertible π ℳ) 0 1 (𝟙 T.left) (𝟙 _) π
      (IsPullback.id_horiz π)).2
      ⟨fun q hq ↦ (ℒ.2.2 q (Nat.pos_of_ne_zero hq)).of_iso
          ((Modules.higherDirectImage π q).mapIso ((Modules.pullbackId _).app ℳ)),
        (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one.{u, u, u} _).1
          (SheafOfModules.IsInvertible.of_iso.{u, u, u}
            ((Modules.higherDirectImage π 0).mapIso ((Modules.pullbackId _).app ℳ)).symm
            (h := ℒ.2.1))⟩
      ⟨t, rfl⟩
  have hχ : ((Modules.pullback ι).obj ℳ).eulerChar κ = 1 := by
    change ℳ.eulerCharFiber π t = 1
    rw [Modules.eulerCharFiber, finsum_eq_single _ 0 (fun q hq ↦ by simp [hfib.1 q hq])]
    simp [hfib.2]
  -- Step 6: `χ(𝒪_{X_t}) = χ(𝒪_X) = 1 - g`
  have hO : Modules.eulerChar κ (SheafOfModules.unit (π.fiber t).ringCatSheaf) =
      1 - (arithmeticGenus k X : ℤ) := by
    -- compare with `X = X ×_k Spec k`, written as a base change so that it carries the
    -- injective resolutions of the hypothesis
    let T₀ : Over (Spec (.of k)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k)))
    let j : T ⟶ T₀ := Over.homMk T.hom (by simp [T₀])
    have : SmoothOfRelativeDimension 1 (Limits.pullback (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k k))) ↘ Spec (.of k)) :=
      smoothOfRelativeDimension_baseChange (X := X) k 1
    have : IsProper (Limits.pullback (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k k))) ↘ Spec (.of k)) :=
      isProper_baseChange (X := X) k
    have : IsProper (Limits.pullback.snd (X ↘ Spec (.of k)) T₀.hom) :=
      MorphismProperty.pullback_snd (P := @IsProper) _ _ ‹_›
    have : GlobalSectionsBijective k X := .of_geometricallyIntegral
    have := SheafOfModules.isQuasicoherent_unit
      (R := (Limits.pullback (X ↘ Spec (.of k)) T₀.hom).ringCatSheaf)
    have : SheafOfModules.IsInvertible.{u, u, u}
        (SheafOfModules.unit (Limits.pullback (X ↘ Spec (.of k)) T₀.hom).ringCatSheaf) :=
      Modules.IsInvertible.sheafOfModules_isInvertible (𝟙_ _)
    have : SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (SheafOfModules.unit (Limits.pullback (X ↘ Spec (.of k)) T₀.hom).ringCatSheaf) :=
      SheafOfModules.IsInvertible.isFiniteLocallyFree.{u, u, u} _
    have : (SheafOfModules.unit
        (Limits.pullback (X ↘ Spec (.of k)) T₀.hom).ringCatSheaf).IsFinitePresentation :=
      SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
    rw [Modules.eulerChar_congr κ (Modules.pullbackObjUnitIso ι).symm,
      Modules.eulerChar_congr κ ((Modules.pullback ι).mapIso
        (Modules.pullbackObjUnitIso (baseChangeMap (X ↘ Spec (.of k)) j)).symm)]
    change Modules.eulerCharFiber _ π t = _
    rw [Modules.eulerCharFiber_pullback_of_isPullback
      (Limits.pullback.snd (X ↘ Spec (.of k)) T₀.hom) _ T.hom _ π
      (isPullback_baseChangeMap (X ↘ Spec (.of k)) j) t, Modules.eulerCharFiber_eq_eulerChar,
      ← arithmeticGenus_pullback (k := k) k]
    convert eulerChar_unit_eq (k := k)
      (X := Limits.pullback (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k k))))
      using 0
    exact Iff.rfl
  have h5 : ((Modules.pullback ι).obj ℳ).degree κ = arithmeticGenus k X := by
    rw [Modules.degree, hχ, hO]
    ring
  rw [h1]
  have : (((D.comap ι).subschemeι ≫ π.fiber t ↘ Spec κ).finrankΓ : ℤ) =
      arithmeticGenus k X := by
    linarith
  exact_mod_cast this

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
  obtain ⟨hinv, h⟩ := isInvertible_zeroLocus_directImageCounit_and_isFiniteLocallyFree σ hσ T ℒ
  exact ⟨hinv, h.toIsFinite, h.toFlat, h.toLocallyOfFinitePresentation,
    finrank_zeroLocus_directImageCounit σ hσ T ℒ⟩

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

/-- **The zero-scheme dictionary is injective.** Two classes `ℒ, ℒ' ∈ F(T)` whose adjunction
morphisms have the same zero scheme `D` are equal.

Writing `𝒩 = f_{T,*} ℒ` and `𝒩' = f_{T,*} ℒ'`, both `ℒ ≅ 𝒪(D) ⊗ f_T^* 𝒩` and
`ℒ' ≅ 𝒪(D) ⊗ f_T^* 𝒩'`
(`AlgebraicGeometry.Scheme.Modules.Hom.nonempty_iso_dual_toModules_tensorObj`).
Pulling back along the section `σ_T`, along which both classes are trivial, gives
`𝒪_T ≅ σ_T^* 𝒪(D) ⊗ 𝒩` and `𝒪_T ≅ σ_T^* 𝒪(D) ⊗ 𝒩'`, hence `𝒩 ≅ 𝒩'` and `ℒ ≅ ℒ'`
(`AlgebraicGeometry.picardFunctorNormalized_eq_of_iso_tensorObj`): this is the inverse
`D ↦ 𝒪(D) ⊗ pr_T^* σ_T^* 𝒪(D)^{-1}` of the blueprint. -/
theorem eq_of_zeroLocus_directImageCounit_eq
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ X ↘ Spec (.of k) = 𝟙 (Spec (.of k)))
    [∀ T : Over (Spec (.of k)),
      HasInjectiveResolutions (Limits.pullback (X ↘ Spec (.of k)) T.hom).Modules]
    (T : Over (Spec (.of k)))
    (ℒ ℒ' : (picardFunctorInvertibleDirectImage (X ↘ Spec (.of k)) σ hσ).toFunctor.obj (op T))
    (h : (Pic.directImageCounit (X ↘ Spec (.of k)) T ℒ.1.1).zeroLocus =
      (Pic.directImageCounit (X ↘ Spec (.of k)) T ℒ'.1.1).zeroLocus) :
    ℒ = ℒ' := by
  -- Both classes are `𝒪(D) ⊗ f_T^* 𝒩` for their own `𝒩 = f_{T,*} ℳ`.
  have key (ℳ : (picardFunctorInvertibleDirectImage (X ↘ Spec (.of k)) σ hσ).toFunctor.obj
      (op T)) :
      Nonempty ((fromSkeleton _).obj ℳ.1.1.val ≅
        (Pic.directImageCounit (X ↘ Spec (.of k)) T ℳ.1.1).zeroLocus.toModulesᵛ ⊗
          (Modules.pullback (Limits.pullback.snd (X ↘ Spec (.of k)) T.hom)).obj
            ((Modules.pushforward (Limits.pullback.snd (X ↘ Spec (.of k)) T.hom)).obj
              ((fromSkeleton _).obj ℳ.1.1.val))) := by
    have := ℳ.1.1.isInvertible
    have := isInvertible_pullback_pushforward σ hσ T ℳ
    exact Modules.Hom.nonempty_iso_dual_toModules_tensorObj _
      (isInvertible_zeroLocus_directImageCounit σ hσ T ℳ).1
  obtain ⟨e⟩ := key ℒ
  obtain ⟨e'⟩ := key ℒ'
  rw [← h] at e'
  exact Subtype.ext (picardFunctorNormalized_eq_of_iso_tensorObj _ σ hσ _ _ _ _ _ e e')

/-- **The adjoint section of the normalized universal module.** Let `ℒ ∈ F(T)` and let `D` be
a point of `Hilb^g_{X/k}(T)` with `ℒ ≅ 𝒪(D) ⊗ f_T^* 𝒩` for an invertible `𝒪_T`-module `𝒩`. Then
the zero scheme of the adjunction morphism `φ : f_T^* f_{T,*} ℒ ⟶ ℒ` is `D`.

The blueprint states this for the universe `T = H = Hilb^g_{X/k}`, the universal divisor
`D = D_univ` and the normalized universal module
`ℒ_H = 𝒪(D_univ) ⊗ pr_H^* σ_H^* 𝒪(D_univ)^{-1}` restricted to the open `W` where it lies in
`F`; the statement here is its pullback to an arbitrary `T`, which is the form used in
`AlgebraicGeometry.isRepresentable_picardFunctorInvertibleDirectImage`.

The canonical section `1` of `𝒪(D)`, twisted by `f_T^* 𝒩`, is a morphism
`s : f_T^* 𝒩 ⟶ ℒ` with zero scheme `D`; it factors as `f_T^* t ≫ φ` through its adjoint
`t : 𝒩 ⟶ f_{T,*} ℒ`, so `Z(φ) ⊆ Z(s) = D`. Both are points of `Hilb^g_{X/k}(T)`
(`AlgebraicGeometry.isInvertible_zeroLocus_directImageCounit`), hence they are equal.

(blueprint: `lem-pc-universal-adjoint-section`) -/
theorem zeroLocus_directImageCounit_eq_of_iso
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ X ↘ Spec (.of k) = 𝟙 (Spec (.of k)))
    [∀ T : Over (Spec (.of k)),
      HasInjectiveResolutions (Limits.pullback (X ↘ Spec (.of k)) T.hom).Modules]
    (T : Over (Spec (.of k)))
    (ℒ : (picardFunctorInvertibleDirectImage (X ↘ Spec (.of k)) σ hσ).toFunctor.obj (op T))
    {D : (Limits.pullback (X ↘ Spec (.of k)) T.hom).IdealSheafData}
    (hD : IsHilbertSubscheme (X ↘ Spec (.of k)) (arithmeticGenus k X) T D)
    (N : T.left.Modules) [SheafOfModules.IsInvertible.{u, u, u} N]
    (e : (fromSkeleton _).obj ℒ.1.1.val ≅
      D.toModulesᵛ ⊗ (Modules.pullback (Limits.pullback.snd (X ↘ Spec (.of k)) T.hom)).obj N) :
    (Pic.directImageCounit (X ↘ Spec (.of k)) T ℒ.1.1).zeroLocus = D := by
  set π := Limits.pullback.snd (X ↘ Spec (.of k)) T.hom
  have hDinv := hD.isInvertible
  have := hDinv.isInvertible_dual_toModules
  have : SheafOfModules.IsInvertible.{u, u, u} D.toModulesᵛ :=
    Modules.IsInvertible.sheafOfModules_isInvertible _
  have : SheafOfModules.IsInvertible.{u, u, u} ((Modules.pullback π).obj N) := .pullback ‹_›
  have := ℒ.1.1.isInvertible
  have := isInvertible_pullback_pushforward σ hσ T ℒ
  have : SheafOfModules.IsInvertible.{u, u, u}
      (𝟙_ (Limits.pullback (X ↘ Spec (.of k)) T.hom).Modules) :=
    Modules.IsInvertible.sheafOfModules_isInvertible _
  -- the canonical section `1` of `𝒪(D)`, twisted by `f_T^* 𝒩`, has zero scheme `D`
  obtain ⟨s, hs⟩ := hDinv.exists_zeroLocus_eq
  let s₁ : (Modules.pullback π).obj N ⟶ (fromSkeleton _).obj ℒ.1.1.val :=
    (λ_ _).inv ≫ (s ▷ _) ≫ e.inv
  have hs₁ : s₁.zeroLocus = D := by
    rw [← hs, ← Modules.Hom.zeroLocus_whiskerRight s ((Modules.pullback π).obj N)]
    exact Modules.Hom.zeroLocus_eq_of_arrowIso _ _ (Arrow.isoMk (λ_ _).symm e (by simp [s₁]))
  -- it factors through the adjunction morphism
  let t := (Modules.pullbackPushforwardAdjunction π).homEquiv _ _ s₁
  have ht : (Modules.pullback π).map t ≫ Pic.directImageCounit (X ↘ Spec (.of k)) T ℒ.1.1 =
      s₁ := by
    have h := (Modules.pullbackPushforwardAdjunction π).homEquiv_counit (g := t)
    rw [Equiv.symm_apply_apply] at h
    exact h.symm
  have hle := Modules.Hom.zeroLocus_comp_le ((Modules.pullback π).map t)
    (Pic.directImageCounit (X ↘ Spec (.of k)) T ℒ.1.1)
  rw [ht, hs₁] at hle
  exact (hD.eq_of_le (isInvertible_zeroLocus_directImageCounit σ hσ T ℒ).2 hle).symm

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

Let `D_univ ⊆ X_H` be the universal divisor and `ℒ_H = 𝒪(D_univ) ⊗ f_H^* σ_H^* 𝒪(D_univ)^{-1}`
the normalized universal module, a point of `Pic_{X/k,σ}(H)`. Since `F ⊆ Pic_{X/k,σ}` is open
(`AlgebraicGeometry.isOpenImmersion_picardFunctorInvertibleDirectImage_ι`), there is an open
`W ⊆ H` such that `a^* ℒ_H ∈ F(T)` exactly for the `a : T ⟶ H` factoring through `W`. The map
`a ↦ a^* ℒ_H` from `h_W` to `F` is inverse to the zero-scheme dictionary `ℒ ↦ Z(φ_ℒ)` followed
by the classifying map of `Hilb^g_{X/k}`: one composite is the identity by
`AlgebraicGeometry.zeroLocus_directImageCounit_eq_of_iso`, the other one because `ℒ` and
`m^* ℒ_H` are both of the form `𝒪(D) ⊗ f_T^* 𝒩` and normalized
(`AlgebraicGeometry.picardFunctorNormalized_eq_of_iso_tensorObj`).

(blueprint: `sk-thm-picard-f-representable`, `thm-pc-f-representable`) -/
theorem isRepresentable_picardFunctorInvertibleDirectImage [IsSepClosed k]
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ X ↘ Spec (.of k) = 𝟙 (Spec (.of k)))
    [∀ T : Over (Spec (.of k)),
      HasInjectiveResolutions (Limits.pullback (X ↘ Spec (.of k)) T.hom).Modules]
    (H : Over (Spec (.of k)))
    (e : (hilbertPresheaf (X ↘ Spec (.of k)) (arithmeticGenus k X)).RepresentableBy H) :
    ∃ (W : Scheme.{u}) (j : W ⟶ H.left), IsOpenImmersion j ∧
      Nonempty ((picardFunctorInvertibleDirectImage (X ↘ Spec (.of k)) σ hσ).toFunctor
        |>.RepresentableBy (Over.mk (j ≫ H.hom))) := by
  let G := (picardFunctorNormalized (X ↘ Spec (.of k)) σ hσ).toFunctor
  let F := picardFunctorInvertibleDirectImage (X ↘ Spec (.of k)) σ hσ
  -- The universal divisor `D_univ ⊆ X_H` and its pullbacks.
  let Du := (e.homEquiv (𝟙 H)).1
  have hDa {T : Over (Spec (.of k))} (a : T ⟶ H) :
      (e.homEquiv a).1 = Du.comap (baseChangeMap (X ↘ Spec (.of k)) a) := by
    have h := e.homEquiv_comp a (𝟙 H)
    rw [Category.comp_id] at h
    rw [h]
    rfl
  -- The normalized universal module `ℒ_H = 𝒪(D_univ) ⊗ f_H^* (σ_H^* 𝒪(D_univ))^{-1}`.
  let P := Du.toModulesᵛ
  have : Modules.IsInvertible P := (e.homEquiv (𝟙 H)).2.isInvertible.isInvertible_dual_toModules
  let A := (Modules.pullback (sectionBaseChange _ σ hσ H)).obj P
  let M := P ⊗ (Modules.pullback (Limits.pullback.snd (X ↘ Spec (.of k)) H.hom)).obj Aᵛ
  have : SheafOfModules.IsInvertible.{u, u, u} M :=
    Modules.IsInvertible.sheafOfModules_isInvertible M
  have hM : Pic.map (sectionBaseChange _ σ hσ H) (Pic.mk M) =
      Pic.mk (SheafOfModules.unit H.left.ringCatSheaf) := by
    obtain ⟨t⟩ := Modules.nonempty_pullback_tensorObj_iso (sectionBaseChange _ σ hσ H) P
      ((Modules.pullback (Limits.pullback.snd (X ↘ Spec (.of k)) H.hom)).obj Aᵛ)
    obtain ⟨d⟩ := Modules.nonempty_tensorObj_dual_iso_unit A
    exact Pic.eq_iff_nonempty_iso.2 ⟨fromSkeletonToSkeletonIso _ ≪≫
      (Modules.pullback _).mapIso (fromSkeletonToSkeletonIso M) ≪≫ t ≪≫
      whiskerLeftIso A (pullbackSectionBaseChangeSndIso _ σ hσ H _) ≪≫ d ≪≫
      (fromSkeletonToSkeletonIso _).symm⟩
  let LH : G.obj (op H) := ⟨Pic.mk M, hM⟩
  -- `F ⊆ Pic_{X/k,σ}` is open: `ℒ_H` cuts out an open `W ⊆ H`.
  obtain ⟨U, hU⟩ := exists_opens_of_relative_isOpenImmersion
    (isOpenImmersion_picardFunctorInvertibleDirectImage_ι (X ↘ Spec (.of k)) σ hσ) H LH
  -- The pullback of `ℒ_H` along `a : T ⟶ H` is `𝒪(D_a) ⊗ f_T^* a^* (σ_H^* 𝒪(D_univ))^{-1}`.
  have key {T : Over (Spec (.of k))} (a : T ⟶ H) :
      Nonempty ((fromSkeleton _).obj (G.map a.op LH).1.val ≅ (e.homEquiv a).1.toModulesᵛ ⊗
        (Modules.pullback (Limits.pullback.snd (X ↘ Spec (.of k)) T.hom)).obj
          ((Modules.pullback a.left).obj Aᵛ)) := by
    obtain ⟨t⟩ := Modules.nonempty_pullback_tensorObj_iso (baseChangeMap _ a) P
      ((Modules.pullback (Limits.pullback.snd (X ↘ Spec (.of k)) H.hom)).obj Aᵛ)
    rw [hDa] at ⊢
    obtain ⟨i⟩ := (e.homEquiv (𝟙 H)).2.isInvertible.nonempty_pullback_dual_toModules_iso
      (baseChangeMap _ a) (by rw [← hDa]; exact (e.homEquiv a).2.isInvertible)
    have hsq : baseChangeMap (X ↘ Spec (.of k)) a ≫
        Limits.pullback.snd (X ↘ Spec (.of k)) H.hom =
        Limits.pullback.snd (X ↘ Spec (.of k)) T.hom ≫ a.left :=
      Limits.pullback.lift_snd _ _ _
    exact ⟨fromSkeletonToSkeletonIso _ ≪≫
      (Modules.pullback _).mapIso (fromSkeletonToSkeletonIso M) ≪≫ t ≪≫
      (i ⊗ᵢ ((Modules.pullbackComp _ _).app _ ≪≫ (Modules.pullbackCongr hsq).app _ ≪≫
        ((Modules.pullbackComp _ _).app _).symm))⟩
  -- The dictionary `ℒ ↦ Z(φ_ℒ)` inverts `a ↦ a^* ℒ_H`.
  have hA {T : Over (Spec (.of k))} (a : T ⟶ H) (ha : G.map a.op LH ∈ F.obj (op T)) :
      (Pic.directImageCounit (X ↘ Spec (.of k)) T (G.map a.op LH).1).zeroLocus =
        (e.homEquiv a).1 := by
    have : SheafOfModules.IsInvertible.{u, u, u} ((Modules.pullback a.left).obj Aᵛ) :=
      Modules.IsInvertible.sheafOfModules_isInvertible _
    exact zeroLocus_directImageCounit_eq_of_iso σ hσ T ⟨_, ha⟩ (e.homEquiv a).2 _
      (key a).some
  let Φ {T : Over (Spec (.of k))} (ℒ : F.toFunctor.obj (op T)) :
      (hilbertPresheaf (X ↘ Spec (.of k)) (arithmeticGenus k X)).obj (op T) :=
    ⟨_, (isInvertible_zeroLocus_directImageCounit σ hσ T ℒ).2⟩
  have hB {T : Over (Spec (.of k))} (ℒ : F.toFunctor.obj (op T)) :
      G.map (e.homEquiv.symm (Φ ℒ)).op LH = ℒ.1 := by
    have := ℒ.1.1.isInvertible
    have := isInvertible_pullback_pushforward σ hσ T ℒ
    obtain ⟨eℒ⟩ := Modules.Hom.nonempty_iso_dual_toModules_tensorObj _
      (isInvertible_zeroLocus_directImageCounit σ hσ T ℒ).1
    obtain ⟨ea⟩ := key (e.homEquiv.symm (Φ ℒ))
    rw [e.homEquiv.apply_symm_apply] at ea
    exact picardFunctorNormalized_eq_of_iso_tensorObj _ σ hσ _ _ _ _ _ ea eℒ
  -- `h_W ≅ F`.
  let ι : Over.mk (U.ι ≫ H.hom) ⟶ H := Over.homMk U.ι
  have hι {T : Over (Spec (.of k))} (b : T ⟶ Over.mk (U.ι ≫ H.hom)) :
      G.map (b ≫ ι).op LH ∈ F.obj (op T) := by
    rw [hU]
    rintro _ ⟨x, rfl⟩
    rw [← U.range_ι]
    exact ⟨b.left x, by simp [ι]⟩
  have hrange {T : Over (Spec (.of k))} (ℒ : F.toFunctor.obj (op T)) :
      Set.range (e.homEquiv.symm (Φ ℒ)).left ⊆ Set.range U.ι := by
    rw [U.range_ι, ← hU, hB]
    exact ℒ.2
  let lift {T : Over (Spec (.of k))} (ℒ : F.toFunctor.obj (op T)) :
      T ⟶ Over.mk (U.ι ≫ H.hom) :=
    Over.homMk (IsOpenImmersion.lift U.ι _ (hrange ℒ)) (by
      simp only [Over.mk_left, Over.mk_hom]
      rw [IsOpenImmersion.lift_fac_assoc, Over.w])
  have hlift {T : Over (Spec (.of k))} (ℒ : F.toFunctor.obj (op T)) :
      lift ℒ ≫ ι = e.homEquiv.symm (Φ ℒ) := by
    ext
    exact IsOpenImmersion.lift_fac _ _ _
  refine ⟨U, U.ι, inferInstance, ⟨{
    homEquiv {T} := {
      toFun b := ⟨G.map (b ≫ ι).op LH, hι b⟩
      invFun := lift
      left_inv b := ?_
      right_inv ℒ := ?_ }
    homEquiv_comp c b := ?_ }⟩⟩
  · rw [← cancel_mono ι]
    refine (hlift _).trans (e.homEquiv.symm_apply_eq.2 (Subtype.ext ?_))
    exact hA _ (hι b)
  · apply Subtype.ext
    change G.map (lift ℒ ≫ ι).op LH = ℒ.1
    rw [hlift, hB]
  · refine Subtype.ext ?_
    change G.map ((c ≫ b) ≫ ι).op LH = G.map c.op (G.map (b ≫ ι).op LH)
    rw [Category.assoc, op_comp, Functor.map_comp]
    rfl

end AlgebraicGeometry
