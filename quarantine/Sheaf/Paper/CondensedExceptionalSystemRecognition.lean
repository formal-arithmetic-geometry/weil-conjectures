/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.Paper.CondensedExceptionalReconstructionData

/-! # CondensedExceptionalSystemRecognition

Source: current blueprint sec-smooth-purity, reconstruction proof.
(blueprint: lem-pur-condensed-exceptional-system-recognition). -/

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
attribute [local irreducible] WeilConjectures.purCoefficientModel
variable {X Y : Base k} {f : X.scheme ⟶ Y.scheme}
  [f.IsOver (Spec (.of k))] {c : Compactification f}
  (P : Context l k X Y f c)

/-- Transport ordinary Brown recognition to the supplied strict-system coordinates.
Source: blueprint sk-prop-sp-integral-adjunction, tower reconstruction and final
unit/counit paragraph; parent reconstruction proof Steps 1--3.
(blueprint: lem-pur-condensed-exceptional-system-recognition).

Proof: use uniform integral reduction for the input and tests. Apply the ordinary
etale Brown adjunction and its finite/site comparison. Conjugate the resulting
systems by the supplied exact presentation equivalences; their representative and
mate normalizations identify their evaluations with brownLevel. In the supplied
alternative retain its theta. In the single-degree alternative the compatible
level isomorphisms give an isomorphism of the strict degree-r cohomology systems;
good truncation constructs theta with the prescribed evaluations. Componentwise
cohomology detects the lower bound. The input is an etale-origin integral
reduction, so its reconstruction unit and the bounded Brown site unit are
invertible, as is the proper/open origin comparison on the supplied system.
For two systems in degree r, conjugate their maps by good truncation. Faithfulness
of the shifted-heart embedding and componentwise equality of strict sheaf-system
maps turn the given level squares into the whole-system square. This argument
also applies to a supplied theta, since its evaluations agree with the same
normalization. No faithfulness of evaluation on general derived maps is used. -/
theorem condensed_exceptional_system_recognition : Nonempty (SystemRecognition l k P) := by
  sorry

end WeilConjectures.CondensedExceptionalReconstruction
