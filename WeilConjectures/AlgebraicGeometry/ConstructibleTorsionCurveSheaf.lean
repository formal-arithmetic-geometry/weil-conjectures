/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CurveCoefficientPair
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves

/-!
# Blueprint statements

def-weil-pbc-constructible-torsion.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.CurveCoefficientPair

/-- def-weil-pbc-constructible-torsion. -/
def IsConstructible {k : Type u} [Field k] [IsAlgClosed k]
    (P : AlgebraicGeometry.CurveCoefficientPair k) : Prop :=
  Scheme.IsConstructibleEtaleSheafOfSets
    ((sheafCompose P.C.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj P.F)

end AlgebraicGeometry.CurveCoefficientPair
