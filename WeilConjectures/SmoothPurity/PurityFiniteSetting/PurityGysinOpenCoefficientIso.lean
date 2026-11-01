/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityGysinStructure

/-! The canonical coefficient comparison on the punctured affine line is invertible.
This is the explicit comparison used by `gysin_structure_statement`; it is recorded
separately so the statement does not appeal to the legacy support-identification theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport

namespace WeilConjectures.PurityFiniteSetting

/-- The canonical open coefficient map is an isomorphism. -/
theorem gysin_open_coefficient_isIso (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] :
    IsIso (P.gysinOpenCoefficient h Y) := by
  dsimp [gysinOpenCoefficient]
  have hr : IsIso (P.twistEtalePullback h (openImmersion Y)) := by
    apply P.isIso_twistEtalePullback h
    exact P.exponent_isUnit (Line Y) (lineProjection Y ≫ a)
  infer_instance

end WeilConjectures.PurityFiniteSetting
