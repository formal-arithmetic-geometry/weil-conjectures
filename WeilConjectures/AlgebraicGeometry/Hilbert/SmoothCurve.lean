/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Hilbert.Curve

/-!
# Hilbert schemes of points on a smooth curve

Let `X` be a geometrically integral smooth proper curve over a field `k` and `d : ℕ`. This file
gathers the results of `WeilConjectures.AlgebraicGeometry.Hilbert.Curve` into one theorem:
`Hilb^d_{X/k}` is represented by a smooth proper geometrically integral `k`-scheme `H` of
dimension `d`, equal to `Spec k` for `d = 0`; its `T`-points are the relative effective Cartier
divisors of `X_T` which are finite locally free of degree `d` over `T`; and it carries a universal
divisor `D_d ⊆ X ×[k] H` from which every `D_h` and `𝒪(D_h)` is pulled back.

## Main statements

- `AlgebraicGeometry.exists_representableBy_hilbertPresheaf_curve`: the theorem above.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **Hilbert schemes of points on a smooth curve.** For a geometrically integral smooth proper
curve `X` over `k` and `d : ℕ`, the functor `Hilb^d_{X/k}` is represented by a smooth proper
geometrically integral `k`-scheme `H` of dimension `d`, which is `Spec k` for `d = 0`. The
`T`-points of `Hilb^d_{X/k}` are precisely the relative effective Cartier divisors of `X_T`
which are finite locally free of degree `d` over `T`. The universal divisor `D_d ⊆ X ×[k] H`,
classified by `𝟙 H`, is a relative effective Cartier divisor, and the divisor `D_h` classified by
`h : T ⟶ H` and its line bundle `𝒪(D_h)` are the pullbacks of `D_d` and `𝒪(D_d)` along
`X_T ⟶ X ×[k] H`. -/
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
            (Scheme.Modules.pullback (baseChangeMap f h)).obj (e.homEquiv (𝟙 _)).1.toModulesᵛ) := by
  obtain ⟨H, ⟨e⟩⟩ := isRepresentable_hilbertPresheaf_curve f d
  obtain ⟨hprop, hint⟩ :=
    isProper_and_geometricallyIntegral_of_representableBy_hilbertPresheaf_curve f d H e
  obtain ⟨hD, hpull⟩ := isRelativeEffectiveCartier_universal_hilbertPresheaf f e
  refine ⟨H.left, H.hom, smoothOfRelativeDimension_of_representableBy_hilbertPresheaf f
    (isRepresentable_hilbertPresheaf_curve f) d H e, hprop, hint, ?_, fun T I ↦ ?_, e, hD,
    fun T h ↦ ⟨?_, hpull T h⟩⟩
  · rintro rfl
    exact isIso_of_representableBy_hilbertPresheaf_zero f e
  · exact ⟨fun hI ↦ ⟨⟨hI.isInvertible, hI.2.1⟩, hI.1, hI.2.2⟩,
      fun ⟨hD, hfin, hlfp, hrank⟩ ↦ ⟨hfin, hD.2, hlfp, hrank⟩⟩
  · have hh := hilbertPresheaf_homEquiv_comp_val f e h (𝟙 H)
    exact (congrArg (fun φ ↦ (e.homEquiv φ).1) (Category.comp_id h).symm).trans hh

end AlgebraicGeometry
