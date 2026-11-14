/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Module.LocalizedModule.Away
import WeilConjectures.AlgebraicGeometry.AffineLocalizingPresheafSheafification
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Affine values of a presheaf satisfying principal localization

## References

* Stacks Project, Tags 01HV and 009H
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Sheafification preserves affine values when restrictions to principal opens
are localizations. No sheaf condition is assumed on non-affine opens (Stacks, Tags 01HV and 009H).
-/
theorem affineLocalization_sheafification_unit_isIso (T : Scheme.{u})
    (P : _root_.PresheafOfModules.{u} T.ringCatSheaf.obj)
    (hlocal : ∀ (U : T.Opens), IsAffineOpen U → ∀ a : Γ(T, U),
      let : Module Γ(T, U) (P.obj (op (T.basicOpen a))) :=
        Module.compHom _ (T.presheaf.map (homOfLE (T.basicOpen_le a)).op).hom
      IsLocalizedModule.Away a (P.map (homOfLE (T.basicOpen_le a)).op).hom)
    (W : T.Opens) (hW : IsAffineOpen W) :
    IsIso (((PresheafOfModules.sheafificationAdjunction
      (𝟙 T.ringCatSheaf.obj)).unit.app P).app (op W)) := by
  apply isIso_sheafificationUnit_app_of_affine_localizing T P ?_ W hW
  intro U hU a
  let : Module Γ(T, U) (P.obj (op (T.basicOpen a))) :=
    Module.compHom _ (T.presheaf.map (homOfLE (T.basicOpen_le a)).op).hom
  exact hlocal U hU a

end AlgebraicGeometry.Scheme.Modules
