/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionSheaf

/-!
# Blueprint statements

def-weil-pbc-constructible-torsion.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Required definitions for def-weil-pbc-constructible-torsion. -/
structure CurveCoefficientPair (k : Type u) [Field k] [IsAlgClosed k] where
  C : Scheme.{u}
  toSpec : C ⟶ Spec (.of k)
  isCurve : IsCurve toSpec
  F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}
  isTorsion : CategoryTheory.Sheaf.IsTorsion F

end AlgebraicGeometry
