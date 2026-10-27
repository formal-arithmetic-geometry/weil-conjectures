/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Sheaf.Paper.PurCompletedReindexingData

/-! # PurReindexingOrdinaryMate

Source: Stacks Project and the extracted proof of
lem-pur-isomorphism-completed-reduction-reindexing.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.privateModule false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] completedAdicChangeData completedReductionCoefficient
attribute [local irreducible] proEtaleRingModulePullback
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
attribute [local irreducible] CochainComplex.IsKFlatIndependentCoefficients
attribute [local instance 2000] reductionModulesHasDerivedCategory reductionTowerHasDerivedCategory
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The ordinary completed-module mate is the sectionwise isomorphism-square
comparison, with its inverse-image-unit normalization.
Source: extracted proof, step 6; Stacks Tag 07A7.
(blueprint: lem-pur-reindexing-ordinary-mate-sections).
Proof: on a test over Y prime, use the canonical map (v,1) between the two fibre
products to restrict sections of M. Its inverse uses (inv v,1); commutativity and
cancellation of g show that both maps lie over the required tests. They commute
with restrictions and carry the completed coefficient action correctly by the
coefficient composition equation. Under the comma-normalized inverse-image
identification these maps give inverse natural transformations. Their adjunction
transpose is the specified pullback-square comparison followed by the counit:
a local inverse-image section is restricted along (v,W to V), on both sides.
The tensor-unit adjunction and sheafification extend that equality to all
sections. Uniqueness of adjunction transposes identifies this transformation with
purReindexingModuleMate. Evaluation after the inverse-image unit is exactly the
restriction along purReindexingTestSquare displayed below. -/
theorem purReindexingOrdinaryMate
    {X' X Y' Y : Scheme.{t}}
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    [IsIso v] [IsIso g] (sq : ChosenCartesianSquare v p' p g) :
  PurCompletedReindexingSquareOrdinary d sq ∧
  PurCompletedReindexingSquareSections d sq := by sorry

end AlgebraicGeometry.Scheme
