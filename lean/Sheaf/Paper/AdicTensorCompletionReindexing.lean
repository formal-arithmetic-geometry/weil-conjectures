/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.AdicTensorPresentationComparison
public import Sheaf.Paper.ReindexingSystemHomReductionSquare

/-! # The integral quotient-completion reindexing square

Source: BS Remark 6.8.15; Stacks 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option cleanup.letToHave false
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime]

/-- The normalized quotient-completion maps commute with integral inverse image.
This equation concerns integral coefficient operations only, with no realization
or scalar-extension tensor comparison.
Source: BS Definition 3.4.10 and Lemma 6.5.5; Stacks 07A4 and 0941.
(blueprint: lem-sf-adic-tensor-completion-reindexing).

Proof: on flat-term K-flat representatives, use the ordinary pure-tensor comparison
for the completed coefficient inverse image. Reindex every finite quotient of the
tensor tower, preserving its coefficient quotient map and its strict transition.
Test the completion maps in both mapping-fiber coordinates. Product projections
are exactly the specified quotient maps on homogeneous pure sections by the first
normalization clause of each presentation. The shifted coordinates are zero by
the second clause. Thus both entire chain maps agree, without using finite-level
maps to detect arbitrary derived morphisms. The representative normalization clauses
and fully faithful restriction to good pairs descend this chain identity. In the
coherent-system coordinates defining canonicalIntegralPullbackTensor, reindexing
commutes with the limit and the specified unit and counit. Its complete-input
identification is podCompletedToTowerIso. Substitute these identifications on the
tensor and on both inputs to obtain the displayed square. This also proves the
claim for torsion integral inputs and zero complexes: no localization or inversion
of a uniformizer occurs. -/
theorem tensor_completion_reindexing
    (k : Type u) [Field k] [Algebra (Padic l) k] [FiniteDimensional (Padic l) k]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (NX : ConstructibleTensorCompletionPresentation l k X)
    (NY : ConstructibleTensorCompletionPresentation l k Y)
    (K L : sfIntegralConstructibleCategory l k Y) :
    let H := podCompletedDerivedInverseImage l k g
    let TX := (pullbackTensorCalculus l k X).integralClosed.tensor
    let TY := constructibleIntegralTensor l k Y
    let P := constructibleIntegralPullback l k g
    H.map ((tensorPresentationCompletion l k Y NY).app (K.obj, L.obj)) ≫
        (podCompletedToTowerIso l k g (TY.obj (K, L))).hom ≫
        (canonicalIntegralPullbackTensor l k g K L).hom.hom =
      (podCompletedAmbientTensor l k g).hom.app (K.obj, L.obj) ≫
        TX.map (Prod.mkHom (podCompletedToTowerIso l k g K).hom
          (podCompletedToTowerIso l k g L).hom) ≫
        (tensorPresentationCompletion l k X NX).app ((P.obj K).obj, (P.obj L).obj) := by sorry

end WeilConjectures.AdicQbarRealization
