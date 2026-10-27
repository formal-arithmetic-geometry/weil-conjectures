/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.SixFunctors.CoefQbarVerdierData
import Sheaf.CategoryTheory.StageSystemAdjunction

/-! # Descent of the finite exceptional adjunction

Source: blueprint thm-coef-qbar-verdier, proof steps 6--9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] WeilConjectures.CoefQbarTensor
  WeilConjectures.CoefQbarPullback

universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.CoefQbarVerdier
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion transition associator unitor)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

variable {Y : Scheme.{u}} [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [QuasiCompact (Y ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- The actual finite exceptional system descends to an adjunction, and its right
adjoint is the Verdier-pullback-Verdier composite for the specified dualities.
Source: blueprint thm-coef-qbar-verdier, proof steps 6--9
(blueprint: lem-coef-qbar-verdier-exceptional-descent).

Proof: take the exceptional system of RationalOperations at the auxiliary small
closure, using only its finite rational coefficient stages. Its normalized scalar
comparisons obey the tower equations, so they define morphisms of the X and Y
stage systems. The descended functors retain the literal stage. Descend the unit
and counit as compatible natural transformations; their compatibility is the mate
condition on the finite scalar comparisons. StageSystem.Morphism.adjunction gives
the adjunction, with its finite components and triangles, and hence all the unit,
counit and scalar equations in ExceptionalProperties. At each finite stage the
normalized internal-Hom descriptions identify the specified BX and BY rational
dualities with those of RationalOperations: uniqueness of the evaluation transpose
fixes these identifications. Transport its finite exceptional comparison through
these identifications. The resulting comparison and inverse obey the scalar tower
squares, so natural-transformation descent identifies the actual descended right
adjoint with BY.dual.rightOp, pullback.op, BX.dual. The finite pullback object formula
and the two duality comparisons give exactly ExceptionalFormula.normalized.
Identity extensions and zero objects are included in the same finite equations. -/
theorem exceptional_descent (BX : Duality D l hl Ω X) (BY : Duality D l hl Ω Y)
    (c : Compactification f) :
    ∃ A : Exceptional D l hl Ω X f c,
      Nonempty (ExceptionalFormula D l hl Ω X f BX BY c A) := by
  sorry

end WeilConjectures.CoefQbarVerdier
