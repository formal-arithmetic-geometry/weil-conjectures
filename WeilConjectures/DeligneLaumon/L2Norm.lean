/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.CondensedL2Norm
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# The L²-weight parameter on a smooth affine curve

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-purity-real-sheaves/sec-weights-and-the-growth-of-squared-traces/
sk-def-wrp-l2-definition/def-wf-l2-norm.md (blueprint: def-wf-l2-norm).

The underlying complex is a strict Weil pair in the bounded constructible
condensed category.  `complexTraceEnergy` is the closed-point regrouping of the
finite sum over rational points (a degree `d` closed point contributes `d`
points whenever `d ∣ m`), and `weightOfEnergy` is the displayed limsup
supremum, with the empty supremum interpreted in `EReal`.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale Filter
open scoped CategoryTheory.Obj

namespace WeilConjectures.DeligneLaumon

/-- The L²-weight parameter of a bounded constructible Weil complex on a
smooth geometrically connected affine curve over a finite field.

Source: current blueprint `def-wf-l2-norm`, including the setting, the
squared trace sum and the limsup-supremum definition (blueprint:
def-wf-l2-norm).  The strict pair supplies the constructible complex and its
Weil structure; `complexTraceEnergy` renders the alternating stalk trace and
its squared rational-point sum, while `weightOfEnergy` renders the final
limsup and the empty-set value `-∞`.
-/
def l2Weight
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (_hell : ell ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsAffine X₀.left]
    [SmoothOfRelativeDimension 1 X₀.hom]
    [GeometricallyConnected X₀.hom]
    (iota : PadicAlgCl ell →+* ℂ)
    (F : condensedStrictWeilComplex (Profinite.padicAlgClRingObj ell)
      (D.geometricFrobenius X₀).hom) : EReal :=
  NativeL2.complexL2Weight D ell X₀ iota F

end WeilConjectures.DeligneLaumon
