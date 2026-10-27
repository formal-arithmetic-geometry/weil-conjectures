/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F7
-/
module

public import Sheaf.SixFunctors.DiagramPullbackShiftData

/-! # DiagramTensorPullbackShiftDescent

Resolving-model step for the simultaneous diagram-site comparison. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genCtorIdx false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.siteDerivedTensorIndependentCoefficients
  SheafOfModules.KFlatFixedTensor.representativeIso
  CategoryTheory.Functor.mapDerivedCategory
  HomologicalComplex₂.total

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.CochainPullback
open SheafOfModules.DerivedTensorConstraints

namespace WeilConjectures.DiagramPullbackShift

variable (A : ℕ → CommRingCat.{u + 1}) (δ : ∀ n : ℕ, A (n + 1) ⟶ A n)

/-- The normalized pullback comparison preserves bidegrees and inherits the simultaneous shift
square from the actual chain comparison on the whole ringed sequence site.
Source: Stacks sites-cohomology.tex, lemma-pullback-tensor-product (07A4) and
lemma-symmetric-monoidal-derived (0FPT); more-algebra.tex, item-shift-tensor.
(blueprint: lem-pur-diagram-tensor-pullback-shift-descent).

Proof: the total comparison on a bidegree summand is the module comparison
followed by the target summand inclusion, by the direct-sum contraction formula.
It preserves the two degrees. The shift comparison contributes (-1)^(bp) on
both routes; naturality of the module comparison and additivity give their
equality on the direct sum. This proves ChainPullbackCoherence.
Resolve both inputs simultaneously on the whole sequence site. Their
shifts, tensor, and pullbacks remain flat-term K-flat. Substitute the normalized
representative formulas for mu and the constraints at the four vertices.
The exact-functor factorization commutes with shifts and is natural in the
chainShift map. Cancel the invertible representative comparisons and
factorization components. The resulting equation is exactly the second clause
of this chain coherence, localized by DerivedCategory.Q; both routes on a shifted bidegree have
coefficient (-1)^(bp). Naturality and faithful restriction on pairs of resolving
inputs extend the equality to arbitrary derived objects. All maps are maps of
the whole strict system before localization, so nonflat transition maps cause
no change in this calculation. -/
theorem diagramTensorPullbackShiftDescent {X Y : Scheme.{u}} {v : X ⟶ Y}
    (P : Pullback A δ v) (mu : TensorPullback A δ P)
    (TY : TensorConstraints A δ Y) (TX : TensorConstraints A δ X) :
    ChainPullbackCoherence A δ P ∧ mu.ShiftCoherence A δ TY TX := by sorry

end WeilConjectures.DiagramPullbackShift
