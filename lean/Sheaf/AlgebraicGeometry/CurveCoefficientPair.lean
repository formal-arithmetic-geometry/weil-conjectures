/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import Sheaf.AlgebraicGeometry.TorsionEtaleSheaf

/-!
# Curve coefficient pairs

Source: the blueprint of the Weil conjectures, chapter `sec-curve-estimates`, unit
`sk-prop-cd`, node def-weil-pbc-curve-setting (blueprint: def-weil-pbc-curve-setting).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A curve coefficient pair over an algebraically closed field `k` consists of a curve
`C → Spec k` and a torsion abelian sheaf on its small etale site. The curve need not be
nonempty, connected, smooth, proper, or one-dimensional: these are not part of the curve
definition in `def-sc-curves`. Source: blueprint `sec-curve-estimates/sk-prop-cd`,
def-weil-pbc-curve-setting (blueprint: def-weil-pbc-curve-setting). -/
structure CurveCoefficientPair (k : Type u) [Field k] [IsAlgClosed k] where
  C : Scheme.{u}
  toSpec : C ⟶ Spec (.of k)
  isCurve : IsCurve toSpec
  F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}
  isTorsion : C.IsTorsionAbelianSheaf F

end AlgebraicGeometry
