/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactificationBProjectionData
public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
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

/-- Reduction of the ordinary projection, in coefficient-first tensor order.
Source: current blueprint, integral-adjunction-direct-image.proof.md (3), and
 tower-geometric-gamma.proof.md (2)
(blueprint: lem-pur-compactification-b-ordinary-square).

Proof: apply complete_projection_mate_descent to M and K in the ordinary tensor
order. Ordinary pullback and tensor preserve completeness, and compact support
preserves completeness with uniform bounds, by the ordinary operation theorems
and integral_direct_image_tower. The compactification-limit realization and the
actual reconstruction counit supply exactly the target and source comparisons
in that descent theorem. Cancel targetComparison to obtain its projection square.
Conjugate by the ordinary signed symmetries on source and inner tensor. The
reduction tensor comparison commutes with these symmetries: on a homogeneous
pure tensor of degrees a,b both composites have sign (-1)^(ab), and the quotient
scalar has degree zero and moves across the balanced tensor. The representative
normalizations tensor_model and pull_model descend this equality to the entire
system category. Reconstruction is natural, so its component commutes with the
image of the inner symmetry. This gives the displayed coefficient-first square.
Naturality is the composite of the proper and open projection naturality squares
and the two tensor-symmetry naturality squares. No equality of derived morphisms is
inferred from finite evaluations. Zero inputs,
empty schemes, identity compactifications, shifts and ramification preserve the
same signed calculation and the same quotient-unit normalization. -/
theorem ordinary_projection_reduction_square
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
    (M : finiteTorConstructibleIntegralCategory l E X.left)
    (hOpen : IsIso (systemOpenInverse l E m c.i ((red l E m X.left).obj M.obj)
      ((VaryingRing.G (rings l E) (transitions l E) c.g).obj
        ((red l E m Y.left).obj K.obj)))) :
    ((red l E m Y.left).map (ordinaryAlpha l E m c K.obj M.obj) ≫
        reconstruction l E m c AX AZ AY (ordinaryInner l E m f.left K.obj M.obj) ≫
        (systemImage l E c).map
          ((m.tensor X.left).hom.app ((ringedPull l E f.left).obj K.obj, M.obj) ≫
            (m.systems X.left).closed.tensor.map
              (Prod.mkHom ((m.pull f.left).hom.app K.obj) (𝟙 _))) =
      (m.tensor Y.left).hom.app (K.obj, (integralImage l E c).obj M.obj) ≫
        (m.systems Y.left).closed.tensor.map
          (Prod.mkHom (𝟙 _) (reconstruction l E m c AX AZ AY M.obj)) ≫
        systemAlpha l E m c ((red l E m Y.left).obj K.obj)
          ((red l E m X.left).obj M.obj) hOpen) ∧
      (∀ (K' : CompleteProjectionDescent.Integral l E Y.left)
        (M' : CompleteProjectionDescent.Integral l E X.left)
        (a : K.obj ⟶ K') (b : M.obj ⟶ M'),
        (m.integral.tensor Y.left).ordinary.tensor.map
            (Prod.mkHom a ((integralImage l E c).map b)) ≫
          ordinaryAlpha l E m c K' M' =
        ordinaryAlpha l E m c K.obj M.obj ≫
          (integralImage l E c).map ((m.integral.tensor X.left).ordinary.tensor.map
            (Prod.mkHom ((ringedPull l E f.left).map a) b))) := by sorry

end AlgebraicGeometry.ProEtale.CompactificationBProjection
