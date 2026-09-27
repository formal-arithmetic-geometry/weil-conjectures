/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
public import WeilConjectures.AlgebraicGeometry.Hilbert.Defs
public import WeilConjectures.AlgebraicGeometry.Picard.Representability

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

Neither a zero scheme `Z(s)` of a section of an invertible sheaf nor the notion of a *relative*
effective Cartier divisor exists in Mathlib or in this project (the absolute notion does, as
`AlgebraicGeometry.IsEffectiveCartierCenter`), and the tensor product and the dual of a sheaf
of modules are the `opaque` placeholders of
`WeilConjectures/AlgebraicGeometry/Modules/Invertible.lean` and
`WeilConjectures/AlgebraicGeometry/Modules/Dual.lean`.
Rather than invent two definitions whose blueprint home is elsewhere, the dictionary is stated
as an existence statement: to `ℒ ∈ F(T)` is attached a quasi-coherent ideal sheaf `D` on `X_T`
whose closed subscheme is an effective Cartier centre and which lies in the Hilbert functor
`Hilb^g_{X/k}(T)`, i.e. is finite, flat and locally of finite presentation of degree `g` over
`T`.  That is exactly the relative statement, and it is the form in which the next two
statements consume it.

Since `AlgebraicGeometry.picardPresheaf` is `Type (u + 1)`-valued while
`AlgebraicGeometry.hilbertPresheaf` is `Type u`-valued, the natural transformation `F ↪ Hilb^g`
is stated after composing the Hilbert functor with `CategoryTheory.uliftFunctor.{u + 1, u}`,
which changes nothing since that functor is fully faithful; this is the same device as the
`CategoryTheory.uliftYoneda` of `WeilConjectures/AlgebraicGeometry/Picard/Representability`.

The structure morphism `X ⟶ Spec k` is carried as an `AlgebraicGeometry.Scheme.Over` instance
and written `X ↘ Spec (.of k)`, as in `WeilConjectures/AlgebraicGeometry/Curve/RiemannRoch`,
because `AlgebraicGeometry.Scheme.genus` needs that instance.

The instance hypothesis `∀ T, HasInjectiveResolutions (X ×[k] T).Modules` is the one nothing
can discharge yet; see `AlgebraicGeometry.Scheme.Modules.isGrothendieckAbelian`.

## Main statements

- `AlgebraicGeometry.exists_isEffectiveCartierCenter_hilbertPresheaf`: the zero-scheme
  dictionary (blueprint `sk-lem-picard-zero-dictionary`).
- `AlgebraicGeometry.exists_injective_natTrans_hilbertPresheaf`: `F` is a subfunctor of the
  Hilbert functor (blueprint
  `sk-the-subsheaf-ff-and-its-representability--remark-1`).
- `AlgebraicGeometry.isRepresentable_picardFunctorInvertibleDirectImage`: `F` is representable
  by an open subscheme of `Hilb^g_{X/k}` (blueprint `sk-thm-picard-f-representable`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  [GeometricallyIntegral (X ↘ Spec (.of k))]

/-- **The zero-scheme dictionary.** Let `ℒ ∈ F(T)`, let `𝒩` be the invertible `𝒪_T`-module with
`Rf_{T,*} ℒ ≅ 𝒩[0]` provided by the definition of `F`, and let
`s ∈ H⁰(X_T, ℒ ⊗ f_T^* 𝒩^{-1})` be the section adjoint to that isomorphism.  Then the zero
scheme `D = Z(s) ⊆ X_T` is a relative effective Cartier divisor on `X_T/T`, finite locally free
of degree `g` over `T`, where `g` is the genus of the curve.

There is no zero scheme of a section and no relative effective Cartier divisor available, so
the conclusion is stated as the existence of the divisor: there is a point `D` of the Hilbert
functor `Hilb^g_{X/k}(T)` whose closed subscheme is moreover an effective Cartier centre in
`X_T`.

(blueprint: `sk-lem-picard-zero-dictionary`) -/
theorem exists_isEffectiveCartierCenter_hilbertPresheaf [IsSepClosed k]
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ X ↘ Spec (.of k) = 𝟙 (Spec (.of k)))
    [∀ T : Over (Spec (.of k)),
      HasInjectiveResolutions (Limits.pullback (X ↘ Spec (.of k)) T.hom).Modules]
    (T : Over (Spec (.of k)))
    (ℒ : (picardFunctorInvertibleDirectImage (X ↘ Spec (.of k)) σ hσ).toFunctor.obj (op T)) :
    ∃ D : (hilbertPresheaf (X ↘ Spec (.of k)) (genus k X)).obj (op T),
      IsEffectiveCartierCenter D.1.subschemeι :=
  sorry

/-- **`F` is a subfunctor of the Hilbert functor.** The dictionary `ℒ ↦ D = Z(s)` of
`AlgebraicGeometry.exists_isEffectiveCartierCenter_hilbertPresheaf` is natural in `T` and
injective, so it exhibits `F` as a subfunctor of `Hilb^g_{X/k}`; the inverse on the image is
`D ↦ 𝒪(D) ⊗ σ_T^* 𝒪(D)^{-1}`.  It is through this injection that the open subscheme
`W ⊆ Hilb^g_{X/k}` of
`AlgebraicGeometry.isRepresentable_picardFunctorInvertibleDirectImage` represents `F`.

`F` takes values in `Type (u + 1)` and `Hilb^g_{X/k}` in `Type u`, so the target is composed
with `CategoryTheory.uliftFunctor.{u + 1, u}`; being fully faithful, this changes neither the
functor nor the injectivity of the components.

(blueprint: `sk-the-subsheaf-ff-and-its-representability--remark-1`) -/
theorem exists_injective_natTrans_hilbertPresheaf [IsSepClosed k]
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ X ↘ Spec (.of k) = 𝟙 (Spec (.of k)))
    [∀ T : Over (Spec (.of k)),
      HasInjectiveResolutions (Limits.pullback (X ↘ Spec (.of k)) T.hom).Modules] :
    ∃ Φ : (picardFunctorInvertibleDirectImage (X ↘ Spec (.of k)) σ hσ).toFunctor ⟶
      hilbertPresheaf (X ↘ Spec (.of k)) (genus k X) ⋙ uliftFunctor.{u + 1, u},
      ∀ T, Function.Injective (Φ.app T) :=
  sorry

/-- **`F` is representable** by an open subscheme of `Hilb^g_{X/k}`: given a `k`-scheme `H`
representing `Hilb^g_{X/k}`, there are a scheme `W` and an open immersion `j : W ⟶ H` such that
`W`, viewed as a `k`-scheme through `j`, represents `F`.

(blueprint: `sk-thm-picard-f-representable`) -/
theorem isRepresentable_picardFunctorInvertibleDirectImage [IsSepClosed k]
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ X ↘ Spec (.of k) = 𝟙 (Spec (.of k)))
    [∀ T : Over (Spec (.of k)),
      HasInjectiveResolutions (Limits.pullback (X ↘ Spec (.of k)) T.hom).Modules]
    (H : Over (Spec (.of k)))
    (e : (hilbertPresheaf (X ↘ Spec (.of k)) (genus k X)).RepresentableBy H) :
    ∃ (W : Scheme.{u}) (j : W ⟶ H.left), IsOpenImmersion j ∧
      Nonempty ((picardFunctorInvertibleDirectImage (X ↘ Spec (.of k)) σ hσ).toFunctor
        |>.RepresentableBy (Over.mk (j ≫ H.hom))) :=
  sorry

end AlgebraicGeometry
