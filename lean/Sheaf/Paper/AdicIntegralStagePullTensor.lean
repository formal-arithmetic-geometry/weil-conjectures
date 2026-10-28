/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.AdicIntegralTensorCoordinates

/-! # Integral-stage coordinates for the canonical common-stage tensor comparison

Source: the representative clauses of the canonical rational and common-stage
pullback/tensor comparisons, and the raw coefficient localization convention.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option cleanup.letToHave false
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime]

/-- The canonical common-stage tensor comparison in integral-stage coordinates.
This equation is solely about the existing coefficient operations; it contains no
ordinary realization, scalar-extension tensorator or reindexing comparison.
Source: Stacks 07A4; the representative clauses of
canonicalRationalPullbackTensor_existsUnique and canonicalCommonStagePullbackTensor_existsUnique.
(blueprint: lem-sf-adic-integral-stage-pull-tensor).

Proof: use the representative clause of the common-stage comparison at E, which
contains the compositum of the two identical input stages. Expand integralStageTensorIso
using stageTensorFormula. Its two normalized identity scalar-extension unitors cancel
the transition comparisons on the two inputs. The remaining representative is the
inclusion at E of the canonical rational pullback/tensor comparison. Its representative
clause identifies it with localization of the canonical integral comparison. The literal
object equations for rational tensor and pullback are precisely tensorIntegralObjectIso
and the second factor of integralStagePullIso. Functoriality of localization and stage
inclusion therefore gives the displayed equality after these transports. All transports
are isomorphisms, so they can be cancelled. This argument uses no enlargement of K or L,
no ordinary realization, and is valid also for the zero pair. -/
theorem integral_stage_pull_tensor
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (K L : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y) :
    let P := constructibleIntegralPullback l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g
    let TY := constructibleIntegralTensor l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y
    let JY := tensorStage l Y E
    let JX := tensorStage l X E
    let G := commonStageDerivedPullback l (PadicAlgCl l) g
    let TX := commonStageDerivedTensor l (PadicAlgCl l) X
    G.map (integralStageTensorIso l Y E K L).hom ≫
        (canonicalCommonStagePullbackTensor l (PadicAlgCl l) g (JY.obj K) (JY.obj L)).hom ≫
        TX.map (Prod.mkHom (integralStagePullIso l g E K).hom
          (integralStagePullIso l g E L).hom) =
      (integralStagePullIso l g E (TY.obj (K, L))).hom ≫
        JX.map (canonicalIntegralPullbackTensor l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g K L).hom ≫
        (integralStageTensorIso l X E (P.obj K) (P.obj L)).hom := by
  sorry

end WeilConjectures.AdicQbarRealization
