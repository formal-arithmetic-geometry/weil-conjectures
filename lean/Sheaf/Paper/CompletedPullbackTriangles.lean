/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.PbcActualStrictPullback
public import Sheaf.Paper.IntrinsicCompletionCompleted
public import Mathlib.CategoryTheory.Triangulated.Functor
import Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Sheaf.Algebra.Homology.DiagramKFlatReplacements
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Paper.CompletedRlimFunctor
import Sheaf.Paper.PbcQbarCompletedPullback

/-! # Completed pullback preserves shifts and distinguished triangles
Source: literature/stacks-project/proetale.tex, Tag 099N (2),(5), with
`derived.tex`, Tag 05SE, and `sites-cohomology.tex`, Tag 0941
(blueprint: lem-cbc-completed-pullback-triangles).

The specified strict-tower completed pullback has coherent shift comparisons,
and it carries distinguished triangles whose vertices are intrinsically derived
complete to distinguished image triangles.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option warn.sorry false
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme

variable {A : Type (u + 1)} [CommRing A]
variable {X Y : Scheme.{u}} (g : X ⟶ Y)
variable (d : AdicCoefficientDatum A)

/-- The strict-tower completed pullback has coherent shifts and preserves
ambient distinguished triangles on intrinsically derived-complete vertices.
Source: literature/stacks-project/proetale.tex, Tag 099N (2),(5), with
`derived.tex`, Tag 05SE, and `sites-cohomology.tex`, Tag 0941
(blueprint: lem-cbc-completed-pullback-triangles).

Proof:
1. The additive reduction-tower construction preserves shifts and mapping cones.
K-flat resolutions and invariance on resolving quasi-isomorphisms are supplied
by `def-weil-pbc-adic-coefficient-datum`. Apply
`lem-pur-left-derived-from-kflat-class` to obtain the exact reduction functor R.
2. Levelwise module pullback along the specified completed coefficient map is
additive, so preserves the shift signs and cone differential matrix.
`lem-weil-pbc-diagram-kflat-replacements` gives strict objectwise K-flat
flat-term replacements and quasi-isomorphism invariance. The same resolving-class
theorem makes its total derived functor V exact; no underived flatness is assumed.
3. By `prop-weil-pbc-rlim-functoriality`, strict-tower derived inverse limit L
is exact. Thus LVR sends the ambient distinguished triangle to a distinguished
triangle. `pbcActualCompletedPullback_tower` in the recorded completed-pullback
dependency identifies its restriction to complete inputs, naturally and with
its quotient augmentation, with the completion-reflector presentation
`pbcActualCompletedPull` used here. Transport the triangle along that comparison.
4. The tensor, product and mapping-fiber formulas defining intrinsic completion
commute with shifts, including its unit, so the complete-object domain is stable
under shifts. Iterate the three exact-functor comparisons for positive integers,
use inverse comparisons for negative integers and the identity for zero.
Compose them as LV(sigma_R), L(sigma_V), sigma_L. Naturality and the zero and
addition identities follow from those of the factors; in mixed signs inverse
factors cancel. The last arrow is the image of the original last arrow followed
by this comparison at 1, exactly as in mapTriangle. The completion-reflector
presentation has the corresponding unit-normalized ordinary-pullback/completion
shift structure on the ambient category; on complete inputs the natural
unit-compatible comparison identifies it with this tower construction.
No constructibility or Noetherian hypothesis on the schemes is used.
-/
theorem completedPullback_preserves_shifts_distinguished
    (g : X ⟶ Y) (d : AdicCoefficientDatum A) :
    ∃ h : (pbcActualCompletedPull g d).CommShift ℤ,
      (fun [shift : (pbcActualCompletedPull g d).CommShift ℤ] ↦
        ∀ (T : Triangle (PbcCompletedDerived Y d)),
          T ∈ distTriang _ →
          PbcIsIntrinsicallyComplete Y d T.obj₁ →
          PbcIsIntrinsicallyComplete Y d T.obj₂ →
          PbcIsIntrinsicallyComplete Y d T.obj₃ →
          (pbcActualCompletedPull g d).mapTriangle.obj T ∈ distTriang _)
        (shift := h) := by
  sorry

end AlgebraicGeometry.Scheme
