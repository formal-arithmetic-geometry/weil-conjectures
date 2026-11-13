/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineFreeBasisGerms
import WeilConjectures.AlgebraicGeometry.TildeScalarSectionAction
import WeilConjectures.AlgebraicGeometry.AffineChartScalarTransport

/-! # Scalar action on sections after affine sheafification

Source: Stacks Project, Tags 01HV, 01IB and 0098.
-/

@[expose] public section
universe u
namespace AlgebraicGeometry.Scheme

/-- Affine sheafification and ordinary direct image carry multiplication by `a` to
multiplication by `a` on sections over the affine open, for every section.

Source: Stacks Project, Tag 01HV, Lemma 26.5.4 (7), Tag 01IB, and Tag 0098. -/
theorem affineScalarEnd_section_action (X : Scheme.{u}) (U : X.Opens)
    (hU : IsAffineOpen U) (a : Γ(X, U)) :
    let P := SheafOfModules.pushforward.{u}
      (SheafOfModules.pushforwardOver (R := moduleRings X.toRingedSpace) U)
    ∀ m : (P.obj ((affinePerfectSheafification X U hU).obj
        (ModuleCat.of Γ(X, U) Γ(X, U)))).val.obj (.op U),
      (P.map ((affinePerfectSheafification X U hU).map
        (affineScalarEnd X U a))).val.app (.op U) m = a • m := by
  apply affine_chart_scalar_transport X U hU a
    ((AlgebraicGeometry.tilde.functor Γ(X, U)).obj (ModuleCat.of Γ(X, U) Γ(X, U)))
    ((AlgebraicGeometry.tilde.functor Γ(X, U)).map (affineScalarEnd X U a))
  intro V s
  exact tilde_scalar_section_action Γ(X, U) (ModuleCat.of Γ(X, U) Γ(X, U)) a
    (affineScalarEnd X U a) (fun _ ↦ rfl) V s

end AlgebraicGeometry.Scheme
