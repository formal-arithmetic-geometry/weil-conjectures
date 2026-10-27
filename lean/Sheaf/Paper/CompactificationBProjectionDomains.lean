/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z7
-/
module

public import Sheaf.Paper.CompactificationBProjectionData
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # A step of compactification projection reduction -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures WeilConjectures.IntegralSystemRealization

namespace AlgebraicGeometry.ProEtale.CompactificationBProjection
open CompleteProjectionDescent

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (m : DescentModels l E)

/-- The completion units and the domains needed for the projection comparison.
Source: current blueprint, integral-adjunction-direct-image.proof.md (1)--(3)
(blueprint: lem-pur-compactification-b-projection-domains).

Proof: ordinary pullback preserves integral constructibility and completeness by
IntegralTensorPullback.preserves_and_completed. Ordinary tensor preserves these
properties by integralTensorProduct. Apply integral_direct_image_tower to M and to
the inner tensor; its uniform bound widens the Tor interval by 2d. Pullback retains
Tor bounds and tensor adds them, by sf_pullback_torAmplitude and
finiteCoefficient_tensor_ctf. The normalized reduction equivalence identifies all
these reductions with normalized constructible towers. Its actual unit, followed
by the published tensor and pullback quotient comparisons, gives precisely innerUnit
and sourceUnit, hence the isomorphisms h and v. The tower projection formula makes
the open inverse factor invertible. The compactification-limit realization applies:
c.i is quasi-compact since c.i followed by the proper, hence quasi-separated, c.g
is f. Its comparison, transposed by the actual reduction/limit counit, is exactly
reconstruction. This proves the two reconstruction isomorphisms. Transport domain
membership along these isomorphisms and along the tensor/pullback reduction
isomorphisms to obtain the displayed system-image and tensor domains. Every
comparison is on the whole system, so common bounds and transitions are retained.
The zero inputs, identity morphism, empty schemes, and ramified coefficients need
no exclusions; the cofinal ell-power subsequence preserves all these properties. -/
theorem completion_projection_domains
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    (X Y : Over (Scheme.Spec.obj (op (CommRingCat.of D.k))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left]
    [IsSeparated f.left] (c : Compactification f.left)
    (AX : SpNormalizedEquivalence l E X.left (m.abelian X.left) (m.red X.left))
    (AZ : SpNormalizedEquivalence l E c.Z (m.abelian c.Z) (m.red c.Z))
    (AY : SpNormalizedEquivalence l E Y.left (m.abelian Y.left) (m.red Y.left))
    (K : finiteTorConstructibleIntegralCategory l E Y.left)
    (M : finiteTorConstructibleIntegralCategory l E X.left) :
    ∃ (h : ordinaryInner l E m f.left K.obj M.obj ≅
        completedInner l E f.left K.obj M.obj)
      (v : ordinarySource l E m c K.obj M.obj ≅
        completedSource l E c K.obj M.obj)
      (hOpen : IsIso (systemOpenInverse l E m c.i ((red l E m X.left).obj M.obj)
        ((VaryingRing.G (rings l E) (transitions l E) c.g).obj
          ((red l E m Y.left).obj K.obj)))),
      h.hom = innerUnit l E m f.left K.obj M.obj ∧
      v.hom = sourceUnit l E m c K.obj M.obj ∧
      finiteTorConstructibleIntegral l E X.left (completedInner l E f.left K.obj M.obj) ∧
      finiteTorConstructibleIntegral l E Y.left (completedSource l E c K.obj M.obj) ∧
      finiteTorConstructibleIntegral l E Y.left ((integralImage l E c).obj M.obj) ∧
      finiteTorConstructibleIntegral l E Y.left ((integralImage l E c).obj
        (completedInner l E f.left K.obj M.obj)) ∧
      normalized l E m X.left ((red l E m X.left).obj M.obj) ∧
      normalized l E m Y.left ((red l E m Y.left).obj K.obj) ∧
      normalized l E m X.left ((red l E m X.left).obj
        (completedInner l E f.left K.obj M.obj)) ∧
      normalized l E m Y.left ((red l E m Y.left).obj
        (completedSource l E c K.obj M.obj)) ∧
      normalized l E m Y.left
        ((systemImage l E c).obj ((red l E m X.left).obj
        (completedInner l E f.left K.obj M.obj))) ∧
      normalized l E m Y.left ((red l E m Y.left).obj
        ((integralImage l E c).obj M.obj)) ∧
      normalized l E m Y.left ((red l E m Y.left).obj
        ((integralImage l E c).obj (completedInner l E f.left K.obj M.obj))) ∧
      normalized l E m X.left ((m.systems X.left).closed.tensor.obj
        ((VaryingRing.G (rings l E) (transitions l E) f.left).obj
          ((red l E m Y.left).obj K.obj), (red l E m X.left).obj M.obj)) ∧
      normalized l E m Y.left ((m.systems Y.left).closed.tensor.obj
        ((red l E m Y.left).obj K.obj,
          (systemImage l E c).obj ((red l E m X.left).obj M.obj))) ∧
      normalized l E m Y.left ((systemImage l E c).obj
        ((m.systems X.left).closed.tensor.obj
          ((VaryingRing.G (rings l E) (transitions l E) f.left).obj
            ((red l E m Y.left).obj K.obj), (red l E m X.left).obj M.obj))) ∧
      IsIso (reconstruction l E m c AX AZ AY M.obj) ∧
      IsIso (reconstruction l E m c AX AZ AY (completedInner l E f.left K.obj M.obj)) := by sorry

end AlgebraicGeometry.ProEtale.CompactificationBProjection
