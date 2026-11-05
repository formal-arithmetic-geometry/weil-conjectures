/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityVerdierUnitIso
public import WeilConjectures.WeilSheaf.SmoothPurityDescendedPointUnit

/-!
# Relative A1' for the descended exchange, by Verdier duality

Let `k` be a finite field with algebraic closure `k̄`, and `f : X ⟶ Y` a morphism of separated
`k`-schemes of finite type, with geometric fibre `f̄ : X̄ ⟶ Ȳ`. For the compact-support base change
isomorphism `descendedShriekGeometricExchange` of `f` along `k ⟶ k̄` (built from the chosen
compactification `X --j--> Z --p--> Y` of `f` and its geometric fibre), the exceptional base
change map at the unit `πX^* Rf^! ℚ̄_ℓ ⟶ Rf̄^! ℚ̄_ℓ` (`smoothUnitBaseChange`) is invertible
(`isIso_smoothUnitBaseChange_descendedShriekGeometricExchange`). No smoothness or properness of
`f` is needed, and `Y` is arbitrary: this is the relative form of
`isIso_smoothUnitBaseChange_descendedShriekGeometricExchange_point`.

## Proof

The open factor `j` has an invertible mate in general
(`isIso_smoothUnitBaseChange_fieldCompactification_of_proper`). For the proper factor
`p : Z ⟶ Y`, the base change map `πZ^* Rp^! ℚ̄_ℓ ⟶ Rp̄^! ℚ̄_ℓ` is invertible by the endomorphism
trick (`isIso_upperShriekBaseChangeOfMap_app_unit_of_iso`), fed with the isomorphism
`πZ^* Rp^! ℚ̄_ℓ ≅ Rp̄^! ℚ̄_ℓ` obtained by Verdier duality
(`upperShriekUnitIsoOfDualizingComplexIso`): biduality at the unit, the exceptional internal hom
exchange, the commutation of the weakly étale `πZ^*` with internal homs, and the point case of A1'
for `Z` and `Y` (`geometricFiberDualizingComplexIso`).
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (l : ℕ) [Fact l.Prime] {k : Type u} [Field k] [Finite k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

end AlgebraicGeometry.ProEtale.CondensedRing
