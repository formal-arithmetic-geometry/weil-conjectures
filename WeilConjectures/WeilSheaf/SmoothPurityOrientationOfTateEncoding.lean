/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangeOrientation
public import WeilConjectures.WeilSheaf.SmoothPurityDescendedVerdierUnit

/-!
# The Weil orientation from the Tate encoding alone

`exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso_of_unitBaseChange` derives the
Weil orientation `Rf^! ℚ̄_ℓ ≅ ℚ̄_ℓ(d)[2d]` of a smooth `f : X ⟶ Y` from the Tate encoding `α`
(A3) and the invertibility of the exceptional base change map at the unit along `k₀ ⟶ k̄₀` (A1').
The latter now holds for every `f`
(`ProEtale.CondensedRing.isIso_smoothUnitBaseChange_descendedShriekGeometricExchange`), so only
`α` remains (`exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso_of_tateEncoding`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.WeilComplex

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

variable {X Y : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

variable (d : ℕ) [SmoothOfRelativeDimension d f] [HasUpperShriek k₀ l f]

end AlgebraicGeometry.WeilComplex
