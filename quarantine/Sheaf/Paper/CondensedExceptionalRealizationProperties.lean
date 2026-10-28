/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.Paper.CondensedExceptionalReconstructionData

/-! # Realization properties for condensed exceptional reconstruction
Source: current blueprint sec-smooth-purity, reconstruction proof.
(blueprint: lem-pur-condensed-exceptional-realization-properties). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
attribute [local instance high] AlgebraicGeometry.strictEtaleLevelDerived
  AlgebraicGeometry.strictEtaleSystemDerived
  WeilConjectures.PurityFiniteSetting.clopenProEtaleSystemDerived
  WeilConjectures.PurityFiniteSetting.clopenProEtaleLevelDerived
attribute [local semireducible] AlgebraicGeometry.exceptionalProSystemDerived
  AlgebraicGeometry.exceptionalProLevelDerived
attribute [local irreducible] HasDerivedCategory.standard
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedExceptionalReconstruction
open CondensedERealization CompactSupportCondensedRealization PurityFiniteSetting
variable (l : ℕ) [Fact l.Prime] (k : Type u) [_root_.Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
attribute [local instance] CondensedERealization.At.encodingAdditive
  CondensedERealization.At.encodingInverseAdditive
attribute [local irreducible] WeilConjectures.purCoefficientModel

/-- The regular coefficient, scalar unit and all integer shifts have the exact normalized
properties required by RealizationProperties.
Source: blueprint sk-prop-sp-integral-adjunction and sk-prop-sp-rational, scalar
extension construction; parent reconstruction proof Step 7.
(blueprint: lem-pur-condensed-exceptional-realization-properties).

Proof: the completed rank-one coefficient has constant rank-one reductions with their
quotient cocycle and invertible completion unit, hence is bounded constructible complete.
K-flat shifts preserve the common finite cohomological interval and etale origins, and
the derived inverse limit commutes with these shifts. Define the section map by the
completed coefficient map followed by section encoding and closure inclusion. Its
normalized transpose is multiplication B tensor_A A to B, with inverse b tensor 1.
Flatness and exact coefficient encoding preserve this isomorphism in the derived
categories. The natural comparison between scalar extension and the recorded realization,
whiskered by shifts and the canonical commShiftIso, has precisely the required
component formula. -/
theorem condensed_exceptional_realization_properties
    (D : CondensedERealization.Data l (Field.{u} l) k) :
    Nonempty (RealizationProperties l k D) := by
  sorry

end WeilConjectures.CondensedExceptionalReconstruction
