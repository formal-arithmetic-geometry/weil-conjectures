/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.DerivedPullbackTensorConstraints

/-! Fixed-stage square for the common-stage pullback/tensor composition representative.

Source: Stacks 07A4 and 0941, and the finite coefficient-field paragraph of the
common-stage composition proof.  At one coefficient field containing all stages,
the prescribed representative formulas reduce the two composites to the rational
pullback/tensor composition equation.  This theorem records that fixed-stage
calculation separately from the choice of a representative for the first route.
(blueprint: lem-pur-pullback-tensor-common-stage-composition-finite-representative-stage-equation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false

universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/--
At a fixed common coefficient stage, the rational composition square identifies
the representative of the right route with any representative of the left route.

Source: Stacks 07A4 and 0941, finite coefficient representative calculation.
Proof: enlarge the coefficient field until it contains every object stage and the
chosen representative.  Expand common-stage pullback, tensor, comparison, and
composition maps using their prescribed formulas.  Adjacent comparison
isomorphisms cancel, leaving exactly
`canonicalRationalPullbackTensor_composition` at that finite coefficient.  The
rational composition theorem proves the resulting stage equality, and the
common-stage quotient constructor transports it to the displayed `HEq`.
(blueprint: lem-pur-pullback-tensor-common-stage-composition-finite-representative-stage-equation).
-/
theorem commonStageCompositionFiniteRepresentative_stageEquation {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M N : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (hA : ((commonStageDerivedPullback l Ω (h ≫ f)).obj
      ((commonStageDerivedTensor l Ω Y).obj (M, N))).stage ≤ L)
    (hB : ((commonStageDerivedTensor l Ω Z).obj
      ((commonStageDerivedPullback l Ω h).obj
        ((commonStageDerivedPullback l Ω f).obj M),
        (commonStageDerivedPullback l Ω h).obj
          ((commonStageDerivedPullback l Ω f).obj N))).stage ≤ L)
    (r : ((commonStageDerivedPullback l Ω (h ≫ f)).obj
      ((commonStageDerivedTensor l Ω Y).obj (M, N))).toStage hA ⟶
      ((commonStageDerivedTensor l Ω Z).obj
        ((commonStageDerivedPullback l Ω h).obj
          ((commonStageDerivedPullback l Ω f).obj M),
          (commonStageDerivedPullback l Ω h).obj
            ((commonStageDerivedPullback l Ω f).obj N))).toStage hB)
    (hleft : HEq
      (((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ Z Y (h ≫ f) hZ hY) M N).hom ≫
        ((@commonStageDerivedTensor l _ Ω _ _ _ Z hZ)).map (Prod.mkHom
          (((@pullbackTensorCommonComposition l _ Ω _ _ _ X Y Z f h hX hY hZ) M).hom)
          (((@pullbackTensorCommonComposition l _ Ω _ _ _ X Y Z f h hX hY hZ) N).hom)))
      (GeneralAlgebraicallyClosedCoefficients.ofHom _ _ L hA hB r)) :
    HEq
      (((@pullbackTensorCommonComposition l _ Ω _ _ _ X Y Z f h hX hY hZ)
          (((@commonStageDerivedTensor l _ Ω _ _ _ Y hY)).obj (M, N))).hom ≫
        ((@commonStageDerivedPullback l _ Ω _ _ _ Z X h hZ hX)).map
          ((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ X Y f hX hY) M N).hom ≫
        ((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ Z X h hZ hX)
          (((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj M)
          (((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj N)).hom)
      (GeneralAlgebraicallyClosedCoefficients.ofHom _ _ L hA hB r) := by
  sorry

end WeilConjectures
