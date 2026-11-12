/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Hilbert.Curve

/-!
# Hilbert schemes of points on a smooth curve

Let `X` be a smooth proper geometrically integral curve over a field `k` and `d : ℕ`. This file
collects the results of `WeilConjectures.AlgebraicGeometry.Hilbert.Curve` into the single
theorem of the blueprint: `Hilb^d_{X/k}` is represented by a smooth proper geometrically integral
`k`-scheme `H_d` of dimension `d`, with `H_0 = Spec k`; its `T`-points are the relative effective
Cartier divisors of `X_T` which are finite locally free of degree `d` over `T`; and it carries a
universal divisor `D_d ⊆ X ×[k] H_d` from which every `D_h` and `𝒪(D_h)` is pulled back.

## Main statements

- `AlgebraicGeometry.isHilbertSubscheme_iff_isRelativeEffectiveCartier`: on a smooth relative
  curve, the points of `Hilb^d` are the relative effective Cartier divisors which are finite
  locally free of degree `d`.
- `AlgebraicGeometry.exists_representableBy_hilbertPresheaf_curve`: the theorem above.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- **The points of the Hilbert functor of a smooth relative curve.** If `f : X ⟶ S` is smooth
of relative dimension `1`, a closed subscheme of `X_T` lies in `Hilb^d_{X/S}(T)` if and only if
it is a relative effective Cartier divisor on `X_T/T` which is finite locally free of degree `d`
over `T`. -/
theorem isHilbertSubscheme_iff_isRelativeEffectiveCartier {X S : Scheme.{u}} (f : X ⟶ S)
    [SmoothOfRelativeDimension 1 f] (d : ℕ) (T : Over S)
    (I : (pullback f T.hom).IdealSheafData) :
    IsHilbertSubscheme f d T I ↔ I.IsRelativeEffectiveCartier (pullback.snd f T.hom) ∧
      IsFinite (I.subschemeι ≫ pullback.snd f T.hom) ∧
      LocallyOfFinitePresentation (I.subschemeι ≫ pullback.snd f T.hom) ∧
      ∀ t, (I.subschemeι ≫ pullback.snd f T.hom).finrank t = d := by
  refine ⟨fun hI ↦ ⟨⟨hI.isInvertible, hI.2.1⟩, hI.1, hI.2.2⟩,
    fun ⟨hD, hfin, hlfp, hrank⟩ ↦ ⟨hfin, hD.2, hlfp, hrank⟩⟩

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **Hilbert schemes of points on a smooth curve.** Let `X` be a smooth proper geometrically
integral curve over `k` and `d : ℕ`. Then `Hilb^d_{X/k}` is represented by a smooth proper
geometrically integral `k`-scheme `H_d` of dimension `d`, and `H_0 ≅ Spec k`. For every
`k`-scheme `T`, the `T`-points of `Hilb^d_{X/k}` are the relative effective Cartier divisors
`D ⊆ X_T` which are finite locally free of degree `d` over `T`. The point `D_d` classified by
the identity of `H_d` is a relative effective Cartier divisor of `X ×[k] H_d` over `H_d`, and if
`h : T ⟶ H_d` classifies `D_h`, then `D_h = (1_X × h)^* D_d` and
`𝒪(D_h) ≅ (1_X × h)^* 𝒪(D_d)`, where `𝒪(D)` is the dual of the invertible ideal of `D`.

(blueprint: `theorem-hilbert-schemes-points-smooth-curve`) -/
theorem exists_representableBy_hilbertPresheaf_curve [SmoothOfRelativeDimension 1 f]
    [IsProper f] [GeometricallyIntegral f] (d : ℕ) :
    ∃ (H : Scheme.{u}) (p : H ⟶ Spec (.of k)), SmoothOfRelativeDimension d p ∧ IsProper p ∧
      GeometricallyIntegral p ∧ (d = 0 → IsIso p) ∧
      (∀ (T : Over (Spec (.of k))) (I : (pullback f T.hom).IdealSheafData),
        IsHilbertSubscheme f d T I ↔ I.IsRelativeEffectiveCartier (pullback.snd f T.hom) ∧
          IsFinite (I.subschemeι ≫ pullback.snd f T.hom) ∧
          LocallyOfFinitePresentation (I.subschemeι ≫ pullback.snd f T.hom) ∧
          ∀ t, (I.subschemeι ≫ pullback.snd f T.hom).finrank t = d) ∧
      ∃ e : (hilbertPresheaf f d).RepresentableBy (Over.mk p),
        (e.homEquiv (𝟙 _)).1.IsRelativeEffectiveCartier (pullback.snd f p) ∧
        ∀ (T : Over (Spec (.of k))) (h : T ⟶ Over.mk p),
          (e.homEquiv h).1 = (e.homEquiv (𝟙 _)).1.comap (baseChangeMap f h) ∧
          Nonempty ((e.homEquiv h).1.toModulesᵛ ≅
            (Scheme.Modules.pullback (baseChangeMap f h)).obj
              (e.homEquiv (𝟙 _)).1.toModulesᵛ) := by
  obtain ⟨H, p, hsm, hprop, hint, e, -⟩ := hilbertPresheaf_curve_representable f d
  obtain ⟨hD, hpull⟩ := isRelativeEffectiveCartier_universal_hilbertPresheaf f e
  refine ⟨H, p, hsm, hprop, hint, fun hd ↦ ?_,
    isHilbertSubscheme_iff_isRelativeEffectiveCartier f d, e, hD, fun T h ↦ ⟨?_, hpull T h⟩⟩
  · subst hd
    exact isIso_of_representableBy_hilbertPresheaf_zero f e
  · simpa using hilbertPresheaf_homEquiv_comp_val f e h (𝟙 _)

end AlgebraicGeometry
