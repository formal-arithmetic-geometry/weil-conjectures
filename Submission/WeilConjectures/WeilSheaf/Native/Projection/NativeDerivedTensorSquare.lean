/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Submission.WeilConjectures.WeilSheaf.Native.Projection.NativeTotalTensorSquare
public import Submission.WeilConjectures.WeilSheaf.Native.Projection.NativeDerivedTensorSquareOfTotal

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Localization of the native pullback tensor square -/

@[expose] public noncomputable section

universe u

open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]

/-- The native pullback tensor square on arbitrary derived objects. -/
lemma condensedRealizationTensor_pull_square
    (M N : DerivedCategory (ProEtaleWeilSheaf k₀ l Y)) :
    DerivedPullTensorSquare k₀ l g M N :=
  condensedRealizationTensor_pull_square_of_total k₀ l g
    (condensedRealizationTotalTensor_pull_square k₀ l g) M N

end AlgebraicGeometry.ProEtaleWeilSheaf
