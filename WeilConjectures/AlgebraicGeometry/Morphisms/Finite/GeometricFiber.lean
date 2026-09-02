/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import WeilConjectures.Mathlib.RingTheory.Etale.GeometricPoint

/-!
# The geometric fibre of a morphism over a geometric point

For a morphism of schemes `f : X ⟶ Y` and a point `y : Spec Ω ⟶ Y` with values in a field `Ω`,
the *geometric fibre* of `f` over `y` is the set of points `x : Spec Ω ⟶ X` lifting `y`
(`AlgebraicGeometry.Scheme.Hom.GeometricFiber`). If `f` is finite it is a finite set, and if `f`
is integral and `Ω` is algebraically closed, every point of the scheme-theoretic fibre
`f ⁻¹ {y}` is the image of a point of the geometric fibre.

Both statements are proved in an affine chart. For `f` affine and an affine open `Y₀ ∋ y` with
preimage `X₀ = f ⁻¹ᵁ Y₀`, the square

```
    Spec Γ(X, X₀) --(hY₀.preimage f).fromSpec--> X
          ⌜ |                                    |
    Spec.map (f.app Y₀)                          f
            |                                    |
            v                                    v
      Spec Γ(Y, Y₀) --------hY₀.fromSpec------>  Y
```

is cartesian (`AlgebraicGeometry.IsAffineOpen.isPullback_SpecMap_app_fromSpec`), so the geometric
points of `X` over `y` are the points of the `Γ(Y, Y₀)`-algebra `Γ(X, X₀)` over the point
`Γ(Y, Y₀) →+* Ω` given by `y` (`AlgebraicGeometry.Scheme.Hom.GeometricFiber.equivPointsOver`),
and the ring-theoretic results of `WeilConjectures.Mathlib.RingTheory.Etale.GeometricPoint`
apply.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.GeometricFiber`: the geometric points of `X` over `y`.
- `AlgebraicGeometry.Scheme.Hom.GeometricFiber.equivPointsOver`: the affine description.
- `AlgebraicGeometry.Scheme.Hom.GeometricFiber.overHomEquiv`: the geometric fibre is the
  hom-set from `y` to `f` in the category of schemes over `Y`.
- `AlgebraicGeometry.Scheme.Hom.GeometricFiber.baseChangeEquiv`: forming the geometric fibre
  commutes with base change along a cartesian square.

## Main results

- `AlgebraicGeometry.Scheme.Hom.GeometricFiber.finite`: the geometric fibre of a finite
  morphism is finite.
- `AlgebraicGeometry.Scheme.Hom.GeometricFiber.exists_apply_default_eq`: for `Ω` algebraically
  closed, every point of the fibre of an integral morphism is hit by a geometric point over `y`.
- `AlgebraicGeometry.Scheme.Hom.GeometricFiber.finite_of_isPullback`: the geometric fibre of a
  base change of a finite morphism is finite.

## Implementation notes

`GeometricFiber` is a plain definition rather than an abbreviation, so that the `Finite` instance
below is registered under the head symbol `GeometricFiber` and is not tried on every `Finite`
goal about a subtype. Its subtype API is provided by `GeometricFiber.ext` and
`GeometricFiber.comp_eq`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {Ω : Type u} [Field Ω] (y : Spec (.of Ω) ⟶ Y)

/-- The geometric fibre of `f : X ⟶ Y` over the geometric point `y : Spec Ω ⟶ Y`: the geometric
points `x : Spec Ω ⟶ X` with `x ≫ f = y`. -/
def GeometricFiber : Type u :=
  {x : Spec (.of Ω) ⟶ X // x ≫ f = y}

namespace GeometricFiber

variable {f y}

@[ext]
lemma ext {x x' : GeometricFiber f y} (h : x.1 = x'.1) : x = x' := Subtype.ext h

@[simp]
lemma comp_eq (x : GeometricFiber f y) : x.1 ≫ f = y := x.2

/-- The geometric fibre of `f` over `y` is the hom-set from `y` to `f` in the category of
schemes over `Y`. This is the form in which the geometric fibre indexes the geometric stalks of
a direct image. -/
noncomputable def overHomEquiv : GeometricFiber f y ≃ (Over.mk y ⟶ Over.mk f) where
  toFun x := Over.homMk x.1 x.comp_eq
  invFun u := ⟨u.left, Over.w u⟩
  left_inv _ := rfl
  right_inv _ := rfl

end GeometricFiber

/-- The algebra structure on `Γ(X, f ⁻¹ᵁ Y₀)` over `Γ(Y, Y₀)` given by `f`. -/
@[instance_reducible]
def affineAlgebra {Y₀ : Y.Opens} : Algebra Γ(Y, Y₀) Γ(X, f ⁻¹ᵁ Y₀) := (f.app Y₀).hom.toAlgebra

attribute [local instance] affineAlgebra

@[simp]
lemma algebraMap_affineAlgebra {Y₀ : Y.Opens} :
    algebraMap Γ(Y, Y₀) Γ(X, f ⁻¹ᵁ Y₀) = (f.app Y₀).hom :=
  rfl

section Affine

variable {Y₀ : Y.Opens} (hY₀ : IsAffineOpen Y₀) (hy : y default ∈ Y₀)

include hY₀ in
/-- The sections of `X` over `f ⁻¹ᵁ Y₀` form a finite module over the sections of `Y` over an
affine open `Y₀`, for `f` finite. -/
lemma finite_affineAlgebra [IsFinite f] : Module.Finite Γ(Y, Y₀) Γ(X, f ⁻¹ᵁ Y₀) :=
  RingHom.finite_algebraMap.mp (f.finite_app Y₀ hY₀)

include hY₀ in
/-- The sections of `X` over `f ⁻¹ᵁ Y₀` are integral over the sections of `Y` over an affine
open `Y₀`, for `f` integral. -/
lemma isIntegral_affineAlgebra [IsIntegralHom f] : Algebra.IsIntegral Γ(Y, Y₀) Γ(X, f ⁻¹ᵁ Y₀) :=
  Algebra.isIntegral_def.mpr (f.isIntegral_app Y₀ hY₀)

variable [IsAffineHom f]

namespace GeometricFiber

/-- **The geometric fibre in an affine chart.** The geometric points of `X` over `y` are the
points of the `Γ(Y, Y₀)`-algebra `Γ(X, f ⁻¹ᵁ Y₀)` over the point of `Γ(Y, Y₀)` given by `y`.

This is the universal property of the cartesian square
`AlgebraicGeometry.IsAffineOpen.isPullback_SpecMap_app_fromSpec`, combined with the full
faithfulness of `Spec`. -/
noncomputable def equivPointsOver :
    GeometricFiber f y ≃ RingHom.PointsOver (affinePoint y hy) Γ(X, f ⁻¹ᵁ Y₀) :=
  (Equiv.subtypeEquivRight fun _ ↦ by rw [SpecMap_affinePoint_fromSpec y hy hY₀]).trans <|
    ((hY₀.isPullback_SpecMap_app_fromSpec f).subtypeCompEquiv
        (Spec.map (CommRingCat.ofHom (affinePoint y hy)))).trans <|
      (Equiv.subtypeEquiv Spec.ringHomEquiv.symm fun t ↦ by
        rw [algebraMap_affineAlgebra, Spec.ringHomEquiv_symm_apply, ← Spec.map_comp,
          Spec.map_injective.eq_iff]
        constructor
        · intro h
          rw [← h]
          rfl
        · intro h
          simpa using congrArg CommRingCat.Hom.hom h).symm

@[simp]
lemma equivPointsOver_symm_apply_coe
    (t : RingHom.PointsOver (affinePoint y hy) Γ(X, f ⁻¹ᵁ Y₀)) :
    ((equivPointsOver f y hY₀ hy).symm t).1 =
      Spec.map (CommRingCat.ofHom t.1) ≫ (hY₀.preimage f).fromSpec :=
  rfl

/-- The geometric point corresponding to a point `t` of `Γ(X, f ⁻¹ᵁ Y₀)` factors through the
affine chart `Spec Γ(X, f ⁻¹ᵁ Y₀)`, where it hits the prime `ker t` (by
`AlgebraicGeometry.Spec.map_default_asIdeal`). -/
lemma equivPointsOver_symm_apply_default
    (t : RingHom.PointsOver (affinePoint y hy) Γ(X, f ⁻¹ᵁ Y₀)) :
    ((equivPointsOver f y hY₀ hy).symm t).1 default =
      (hY₀.preimage f).fromSpec (Spec.map (CommRingCat.ofHom t.1) default) :=
  rfl

end GeometricFiber

end Affine

namespace GeometricFiber

/-- **The geometric fibre of a finite morphism is finite.** -/
instance finite [IsFinite f] : Finite (GeometricFiber f y) := by
  obtain ⟨Y₀, hY₀, hy, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := y default) (U := ⊤) trivial
  have := finite_affineAlgebra f hY₀
  exact .of_equiv _ (equivPointsOver f y hY₀ hy).symm

/-- **Every point of the fibre of an integral morphism over a geometric point `y` with values in
an algebraically closed field is the image of a geometric point over `y`.**

This is the analogue for integral morphisms of
`AlgebraicGeometry.Scheme.exists_fac_of_etale_of_isSepClosed`, which proves the same lifting
statement for an étale morphism and a separably closed field. -/
lemma exists_apply_default_eq [IsIntegralHom f] [IsAlgClosed Ω] (x : X) (hx : f x = y default) :
    ∃ t : GeometricFiber f y, t.1 default = x := by
  obtain ⟨Y₀, hY₀, hy, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := y default) (U := ⊤) trivial
  have := isIntegral_affineAlgebra f hY₀
  -- `x` lies in `f ⁻¹ᵁ Y₀`, hence is a prime `𝔮` of `Γ(X, f ⁻¹ᵁ Y₀)`
  have hx₀ : x ∈ Set.range (hY₀.preimage f).fromSpec.base := by
    rw [(hY₀.preimage f).range_fromSpec, Scheme.Hom.coe_preimage, Set.mem_preimage, hx]
    exact hy
  obtain ⟨𝔮, rfl⟩ := hx₀
  -- and `𝔮` lies over `ker (affinePoint y hy)`
  have hcomm : Spec.map (f.app Y₀) 𝔮 =
      Spec.map (CommRingCat.ofHom (affinePoint y hy)) default := by
    apply hY₀.fromSpec.isOpenEmbedding.injective
    calc hY₀.fromSpec (Spec.map (f.app Y₀) 𝔮)
        = (Spec.map (f.app Y₀) ≫ hY₀.fromSpec) 𝔮 := rfl
      _ = ((hY₀.preimage f).fromSpec ≫ f) 𝔮 := by rw [hY₀.SpecMap_app_fromSpec f]
      _ = y default := hx
      _ = (Spec.map (CommRingCat.ofHom (affinePoint y hy)) ≫ hY₀.fromSpec) default := by
          rw [SpecMap_affinePoint_fromSpec]
      _ = hY₀.fromSpec (Spec.map (CommRingCat.ofHom (affinePoint y hy)) default) := rfl
  have h𝔮 : 𝔮.asIdeal.LiesOver (RingHom.ker (affinePoint y hy)) := by
    refine ⟨?_⟩
    have h := congrArg PrimeSpectrum.asIdeal hcomm
    rw [Spec.map_default_asIdeal] at h
    simpa [Ideal.under, Spec.map_apply] using h.symm
  obtain ⟨t, ht⟩ := RingHom.PointsOver.exists_ker_eq (φ := affinePoint y hy) 𝔮.asIdeal
  refine ⟨(equivPointsOver f y hY₀ hy).symm t, ?_⟩
  rw [equivPointsOver_symm_apply_default]
  congr 1
  exact PrimeSpectrum.ext (by rw [Spec.map_default_asIdeal, ht])

end GeometricFiber

section BaseChange

variable {X' Y' : Scheme.{u}} {f' : X' ⟶ Y'} {g' : X' ⟶ X} {g : Y' ⟶ Y}

namespace GeometricFiber

variable {f}

/-- **Forming the geometric fibre commutes with base change.** If

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

is a cartesian square and `y' : Spec Ω ⟶ Y'` is a geometric point of `Y'`, then composing with
`g'` identifies the geometric fibre of `f'` over `y'` with the geometric fibre of `f` over the
image geometric point `y' ≫ g`. -/
noncomputable def baseChangeEquiv (h : IsPullback g' f' f g) (y' : Spec (.of Ω) ⟶ Y') :
    f'.GeometricFiber y' ≃ f.GeometricFiber (y' ≫ g) where
  toFun x' := ⟨x'.1 ≫ g', by rw [Category.assoc, h.w, ← Category.assoc, x'.comp_eq]⟩
  invFun x := ⟨h.lift x.1 y' x.comp_eq, h.lift_snd _ _ _⟩
  left_inv x' := ext <| h.hom_ext (by rw [h.lift_fst]) (by rw [h.lift_snd, x'.comp_eq])
  right_inv x := ext <| h.lift_fst _ _ _

@[simp]
lemma baseChangeEquiv_apply_coe (h : IsPullback g' f' f g) (y' : Spec (.of Ω) ⟶ Y')
    (x' : f'.GeometricFiber y') : (baseChangeEquiv h y' x').1 = x'.1 ≫ g' :=
  rfl

@[simp]
lemma baseChangeEquiv_symm_apply_coe_comp (h : IsPullback g' f' f g) (y' : Spec (.of Ω) ⟶ Y')
    (x : f.GeometricFiber (y' ≫ g)) : ((baseChangeEquiv h y').symm x).1 ≫ g' = x.1 :=
  h.lift_fst _ _ _

@[simp]
lemma baseChangeEquiv_symm_apply_coe_comp_snd (h : IsPullback g' f' f g)
    (y' : Spec (.of Ω) ⟶ Y') (x : f.GeometricFiber (y' ≫ g)) :
    ((baseChangeEquiv h y').symm x).1 ≫ f' = y' :=
  ((baseChangeEquiv h y').symm x).comp_eq

/-- **The geometric fibre of a base change of a finite morphism is finite.** -/
lemma finite_of_isPullback [IsFinite f] (h : IsPullback g' f' f g) (y' : Spec (.of Ω) ⟶ Y') :
    Finite (f'.GeometricFiber y') :=
  .of_equiv _ (baseChangeEquiv h y').symm

variable (f g)

/-- The geometric fibre of the second projection of `Limits.pullback f g` over `y'` is the
geometric fibre of `f` over `y' ≫ g`. This is `baseChangeEquiv` for the square given by
`Limits.pullback f g`. -/
noncomputable def pullbackEquiv (y' : Spec (.of Ω) ⟶ Y') :
    (pullback.snd f g).GeometricFiber y' ≃ f.GeometricFiber (y' ≫ g) :=
  baseChangeEquiv (IsPullback.of_hasPullback f g) y'

@[simp]
lemma pullbackEquiv_apply_coe (y' : Spec (.of Ω) ⟶ Y')
    (x' : (pullback.snd f g).GeometricFiber y') :
    (pullbackEquiv f g y' x').1 = x'.1 ≫ pullback.fst f g :=
  rfl

@[simp]
lemma pullbackEquiv_symm_apply_coe_comp (y' : Spec (.of Ω) ⟶ Y')
    (x : f.GeometricFiber (y' ≫ g)) :
    ((pullbackEquiv f g y').symm x).1 ≫ pullback.fst f g = x.1 :=
  baseChangeEquiv_symm_apply_coe_comp _ _ _

@[simp]
lemma pullbackEquiv_symm_apply_coe_comp_snd (y' : Spec (.of Ω) ⟶ Y')
    (x : f.GeometricFiber (y' ≫ g)) :
    ((pullbackEquiv f g y').symm x).1 ≫ pullback.snd f g = y' :=
  baseChangeEquiv_symm_apply_coe_comp_snd _ _ _

end GeometricFiber

end BaseChange

end AlgebraicGeometry.Scheme.Hom
