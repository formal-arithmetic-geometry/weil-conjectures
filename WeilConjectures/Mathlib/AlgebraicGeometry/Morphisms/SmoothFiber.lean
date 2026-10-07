/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber

/-!
# Smoothness by flatness and smooth fibres

A morphism of schemes is smooth if and only if it is flat, locally of finite presentation, and
all its fibres are smooth over the residue fields.

## Main statements

- `AlgebraicGeometry.smooth_iff_flat_locallyOfFinitePresentation_smooth_fiberToSpecResidueField`:
  the fibrewise criterion for smoothness.

## References

- Stacks Project, Lemma 29.35.3, <https://stacks.math.columbia.edu/tag/01V8>
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- **Smoothness by flatness and smooth fibres** (blueprint `sbc-lem-smooth-criterion`). A
morphism `f : X ⟶ Y` is smooth if and only if it is flat, locally of finite presentation, and
every fibre `X_y ⟶ Spec κ(y)` is smooth. A smooth morphism is flat and locally of finite
presentation, and its fibres are smooth by base change; the converse is
`AlgebraicGeometry.Smooth.of_smooth_fiberToSpecResidueField`. -/
@[stacks 01V8]
theorem smooth_iff_flat_locallyOfFinitePresentation_smooth_fiberToSpecResidueField
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Smooth f ↔ Flat f ∧ LocallyOfFinitePresentation f ∧
      ∀ y, Smooth (f.fiberToSpecResidueField y) :=
  ⟨fun _ ↦ ⟨inferInstance, inferInstance, fun _ ↦ by
    rw [Scheme.Hom.fiberToSpecResidueField]; infer_instance⟩,
    fun ⟨_, _, h⟩ ↦ .of_smooth_fiberToSpecResidueField f h⟩

end AlgebraicGeometry
