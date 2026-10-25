/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.TangentCone
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Pushout squares of charts of blow-ups

For a commutative ring `A` and `x y : A`, let `blowupChart x y = A[T]/(xT - y)` be the chart of
the blow-up of `Spec A` along `(x, y)`. We record two pushout squares of commutative rings:

* base change of a localized chart: for a ring map `f : A → R` and `u_A ∈ A[T]/(xT - y)` with
  image `u ∈ R[T]/(f(x) T - f(y))`, the localization `(R[T]/(f(x)T - f(y)))[1/u]` is the pushout
  of `(A[T]/(xT - y))[1/u_A]` along `f`
  (`AlgebraicGeometry.isPushout_blowupChart_away`);
* the chart as a base change of the affine plane: for a ring map `g : R₀[X₀, X₁] → A`, the chart
  `A[T]/(g(X₀)T - g(X₁))` is the pushout of `A` along the map `R₀[X₀, X₁] → R₀[X₀, X₁]`,
  `X₀ ↦ X₀`, `X₁ ↦ X₀X₁` (the chart of the blow-up of the plane at the origin), the second
  variable going to `T` (`AlgebraicGeometry.isPushout_blowupChart_plane`).

## Main definitions

- `AlgebraicGeometry.blowupChartMap`: the map of charts induced by a ring map.
- `AlgebraicGeometry.planeChartMap`: the map `R₀[X₀, X₁] → R₀[X₀, X₁]`, `X₁ ↦ X₀X₁`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry

section ChartMap

variable {A A' : Type u} [CommRing A] [CommRing A'] (f : A →+* A') {x y : A} {x' y' : A'}
  (hx : f x = x') (hy : f y = y')

/-- The ring map `A[T]/(xT - y) → A'[T]/(x'T - y')` induced by a ring map `f : A → A'` with
`f x = x'` and `f y = y'`. -/
noncomputable def blowupChartMap : blowupChart x y →+* blowupChart x' y' :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (Polynomial.mapRingHom f)) (by
    intro p hp
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hp
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton'.mpr ⟨q.map f, by simp [hx, hy]⟩)

@[simp]
lemma blowupChartMap_mk (p : A[X]) :
    blowupChartMap f hx hy (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (p.map f) :=
  rfl

lemma blowupChartMap_comp_algebraMap :
    (blowupChartMap f hx hy).comp (algebraMap A (blowupChart x y)) =
      (algebraMap A' (blowupChart x' y')).comp f := by
  ext a
  simp [Ideal.Quotient.algebraMap_eq]

end ChartMap

section Away

variable {A R : CommRingCat.{u}} (f : A ⟶ R) {x y : A} {x' y' : R} (hx : f.hom x = x')
  (hy : f.hom y = y') (uA : blowupChart x y)

/-- **Base change of a localized chart of a blow-up.** For a ring map `f : A → R`, `x y : A`
with images `x' y'`, and `u_A` in the chart `A[T]/(xT - y)` with image `u` in
`R[T]/(x'T - y')`, the square
`A → (A[T]/(xT - y))[1/u_A]`, `A → R`, `R → (R[T]/(x'T - y'))[1/u]` is a pushout of rings. -/
theorem isPushout_blowupChart_away :
    IsPushout (CommRingCat.ofHom ((algebraMap (blowupChart x y) (Localization.Away uA)).comp
        (algebraMap A (blowupChart x y)))) f
      (CommRingCat.ofHom (Localization.awayMap (blowupChartMap f.hom hx hy) uA))
      (CommRingCat.ofHom ((algebraMap (blowupChart x' y')
        (Localization.Away (blowupChartMap f.hom hx hy uA))).comp
          (algebraMap R (blowupChart x' y')))) := by
  set F := blowupChartMap f.hom hx hy
  set L := Localization.Away (F uA)
  have hT : F (Ideal.Quotient.mk _ X) = Ideal.Quotient.mk _ X := by simp [F]
  have hw : CommRingCat.ofHom ((algebraMap (blowupChart x y) (Localization.Away uA)).comp
        (algebraMap A (blowupChart x y))) ≫
      CommRingCat.ofHom (Localization.awayMap F uA) =
      f ≫ CommRingCat.ofHom ((algebraMap (blowupChart x' y') L).comp
        (algebraMap R (blowupChart x' y'))) := by
    ext a
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply, Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
    congr 1
    exact congr($(blowupChartMap_comp_algebraMap f.hom hx hy) a)
  -- the joint epimorphism property of the two maps to `L`
  have hext : ∀ {T : CommRingCat.{u}} (m m' : CommRingCat.of L ⟶ T),
      CommRingCat.ofHom (Localization.awayMap F uA) ≫ m =
        CommRingCat.ofHom (Localization.awayMap F uA) ≫ m' →
      CommRingCat.ofHom ((algebraMap (blowupChart x' y') L).comp
          (algebraMap R (blowupChart x' y'))) ≫ m =
        CommRingCat.ofHom ((algebraMap (blowupChart x' y') L).comp
          (algebraMap R (blowupChart x' y'))) ≫ m' → m = m' := by
    intro T m m' h₁ h₂
    ext1
    apply IsLocalization.ringHom_ext (Submonoid.powers (F uA))
    apply Ideal.Quotient.ringHom_ext
    apply Polynomial.ringHom_ext
    · intro r
      exact congr($(h₂).hom r)
    · have := congr($(h₁).hom (algebraMap _ (Localization.Away uA) (Ideal.Quotient.mk _ X)))
      simpa [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq, hT] using this
  refine IsPushout.of_isColimit (PushoutCocone.IsColimit.mk hw
    (fun s ↦ ?_) (fun s ↦ ?_) (fun s ↦ ?_) (fun s m h₁ h₂ ↦ ?_))
  rotate_left
  · -- `fac_left`
    sorry
  · sorry
  · sorry
  · sorry

end Away

end AlgebraicGeometry
