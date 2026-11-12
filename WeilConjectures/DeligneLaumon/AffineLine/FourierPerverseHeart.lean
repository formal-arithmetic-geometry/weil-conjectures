/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.PerverseTStructure
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.TExact

/-!
# The Fourier transform and the perverse heart

For a nontrivial additive character `ψ`, the Fourier–Deligne transform `FT_ψ` of Weil complexes
on the affine line is a t-exact equivalence for the perverse t-structure
(`AlgebraicGeometry.WeilComplex.curvePerverseTStructure`), with quasi-inverse
`FT_{ψ⁻¹}(-)(1)`. Hence it restricts to an exact autoequivalence of the abelian category of
perverse Weil sheaves (blueprint `proposition-fourier-transform-perverse-heart`).

Following the blueprint, `FT_ψ` and its quasi-inverse preserve `ᵖD^{≤n}`
(`AlgebraicGeometry.isCurvePerverseLE_fourierTransform_obj`,
`AlgebraicGeometry.isCurvePerverseLE_fourierTransform_inv_obj`); being mutually inverse, they
preserve the right orthogonals `ᵖD^{≥n}` of the classes `ᵖD^{≤n-1}`.

## Main statements

- `AlgebraicGeometry.tExact_fourierTransform`: `FT_ψ` is t-exact.
- `AlgebraicGeometry.nonempty_fourierTransform_inv_iso`,
  `AlgebraicGeometry.tExact_fourierTransform_inv_comp_tateTwist`: its quasi-inverse is
  `FT_{ψ⁻¹}(-)(1)`, which is t-exact.
- `AlgebraicGeometry.curvePerverseFourierTransform`: the induced autoequivalence of the category
  of perverse Weil sheaves, and `AlgebraicGeometry.exact_curvePerverseFourierTransform`: it is
  exact.

## Implementation notes

A Weil complex carries its Weil structure (`AlgebraicGeometry.WeilComplex` is the derived
category of Weil sheaves), and `FT_ψ` is defined directly on Weil complexes: the Frobenius
compatibilities of the blueprint are built into the functor. Hence the equivalence of perverse
hearts and the equivalence of perverse Weil sheaves of the blueprint are the same functor
`AlgebraicGeometry.curvePerverseFourierTransform`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Triangulated

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

open WeilComplex

/-- `FT_ψ` preserves and reflects the classes `ᵖD^{≤n}`. -/
theorem isCurvePerverseLE_fourierTransform_obj_iff (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1)
    (n : ℤ) (K : WeilComplex k₀ l (affineLine k₀)) :
    ((fourierTransform ψ).obj K).IsCurvePerverseLE n ↔ K.IsCurvePerverseLE n := by
  have := isEquivalence_fourierTransform (l := l) ψ hψ
  exact ⟨fun h ↦ (isCurvePerverseLE_fourierTransform_inv_obj ψ hψ h).of_iso
    ((fourierTransform ψ).asEquivalence.unitIso.app K).symm,
    isCurvePerverseLE_fourierTransform_obj ψ hψ⟩

/-- **The Fourier transform is perverse t-exact**: for a nontrivial additive character `ψ`, the
Fourier–Deligne transform `FT_ψ` of Weil complexes on the affine line is t-exact for the perverse
t-structure. It preserves `ᵖD^{≤n}` by the stalk computation
(`AlgebraicGeometry.isCurvePerverseLE_fourierTransform_obj`), and `ᵖD^{≥n}`, the right
orthogonal of `ᵖD^{≤n-1}`, because its quasi-inverse preserves `ᵖD^{≤n-1}`.
(blueprint: `proposition-fourier-transform-perverse-heart--1`) -/
theorem tExact_fourierTransform (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1) :
    (fourierTransform (l := l) ψ).TExact curvePerverseTStructure curvePerverseTStructure := by
  have := isEquivalence_fourierTransform (l := l) ψ hψ
  exact Functor.tExact_of_preserves_of_reflects_isLE _ _ _ fun Y n ↦
    ⟨fun h ↦ ⟨(isCurvePerverseLE_fourierTransform_obj_iff ψ hψ n Y).1 h.le⟩,
      fun h ↦ ⟨(isCurvePerverseLE_fourierTransform_obj_iff ψ hψ n Y).2 h.le⟩⟩

/-- **Fourier inversion**: the quasi-inverse of `FT_ψ` is `FT_{ψ⁻¹}(-)(1)`, since
`FT_{ψ⁻¹} ∘ FT_ψ ≅ (-)(-1)`. (blueprint: `proposition-fourier-transform-perverse-heart--1`) -/
theorem nonempty_fourierTransform_inv_iso (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1) :
    haveI := isEquivalence_fourierTransform (l := l) ψ hψ
    Nonempty ((fourierTransform ψ).inv ≅
      fourierTransform ψ⁻¹ ⋙ tateTwist k₀ l (affineLine k₀) 1) := by
  have := isEquivalence_fourierTransform (l := l) ψ hψ
  obtain ⟨e⟩ := nonempty_fourierTransform_comp_fourierTransform_inv_iso (l := l) ψ hψ
  let e' : fourierTransform ψ ⋙ fourierTransform ψ⁻¹ ⋙ tateTwist k₀ l (affineLine k₀) 1 ≅ 𝟭 _ :=
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e _ ≪≫
      tateTwistCompTateTwistIso (-1) 1 (by norm_num)
  exact ⟨(Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ e'.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (fourierTransform ψ).asEquivalence.counitIso _ ≪≫
    Functor.leftUnitor _⟩

/-- The quasi-inverse `FT_{ψ⁻¹}(-)(1)` of `FT_ψ` is t-exact for the perverse t-structure.
(blueprint: `proposition-fourier-transform-perverse-heart--1`) -/
theorem tExact_fourierTransform_inv_comp_tateTwist (ψ : AddChar k₀ (PadicAlgCl l))
    (hψ : ψ ≠ 1) :
    (fourierTransform (l := l) ψ⁻¹ ⋙ tateTwist k₀ l (affineLine k₀) 1).TExact
      curvePerverseTStructure curvePerverseTStructure := by
  have := isEquivalence_fourierTransform (l := l) ψ⁻¹ (inv_ne_one.2 hψ)
  have := isEquivalence_tateTwist (k₀ := k₀) (l := l) (X := affineLine k₀) 1
  exact Functor.tExact_of_preserves_of_reflects_isLE _ _ _ fun Y n ↦
    ⟨fun h ↦ ⟨(isCurvePerverseLE_fourierTransform_obj_iff ψ⁻¹ (inv_ne_one.2 hψ) n Y).1
        ((isCurvePerverseLE_tateTwist_iff 1 n _).1 h.le)⟩,
      fun h ↦ ⟨(isCurvePerverseLE_tateTwist_iff 1 n _).2
        ((isCurvePerverseLE_fourierTransform_obj_iff ψ⁻¹ (inv_ne_one.2 hψ) n Y).2 h.le)⟩⟩

/-- The Fourier–Deligne transform `FT_ψ` restricted to perverse Weil sheaves on the affine line:
by perverse t-exactness (`AlgebraicGeometry.isCurvePerverse_fourierTransform_obj_iff`) the
equivalence `FT_ψ` restricts to an autoequivalence of the perverse heart. -/
noncomputable def curvePerverseFourierTransform (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1) :
    (curvePerverse (k₀ := k₀) (l := l)).FullSubcategory ≌
      (curvePerverse (k₀ := k₀) (l := l)).FullSubcategory :=
  haveI := isEquivalence_fourierTransform (l := l) ψ hψ
  (fourierTransform ψ).asEquivalence.congrFullSubcategory
    (funext fun K ↦ propext (isCurvePerverse_fourierTransform_obj_iff ψ hψ K))

/-- The restriction of `FT_ψ` to perverse Weil sheaves is `FT_ψ` on underlying Weil complexes. -/
theorem curvePerverseFourierTransform_functor_comp_ι (ψ : AddChar k₀ (PadicAlgCl l))
    (hψ : ψ ≠ 1) :
    (curvePerverseFourierTransform ψ hψ).functor ⋙ curvePerverse.ι =
      curvePerverse.ι ⋙ fourierTransform ψ :=
  rfl

/-- **The Fourier transform is an exact equivalence of perverse Weil sheaves**: for a nontrivial
`ψ`, the autoequivalence `FT_ψ` of the abelian category of perverse Weil sheaves on the affine
line is exact, as is every equivalence of abelian categories. Since Weil complexes carry their
Weil structure, this is at once the exact equivalence of perverse hearts and the exact equivalence
of perverse Weil sheaves of the blueprint.
(blueprint: `proposition-fourier-transform-perverse-heart--2`,
`proposition-fourier-transform-perverse-heart--3`) -/
theorem exact_curvePerverseFourierTransform (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1) :
    PreservesFiniteLimits (curvePerverseFourierTransform ψ hψ).functor ∧
      PreservesFiniteColimits (curvePerverseFourierTransform ψ hψ).functor :=
  ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry
