/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Free sheaves of modules are quasi-coherent

## Main results

- `SheafOfModules.isQuasicoherent_free`: a free sheaf of modules is quasi-coherent.
- `SheafOfModules.isQuasicoherent_unit`: the unit sheaf of modules is quasi-coherent.
-/

@[expose] public section

universe u v₁ u₁

open CategoryTheory Limits

variable {C : Type u₁} [Category.{v₁} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace SheafOfModules

/-- A free sheaf of modules is quasi-coherent: it is the cokernel of the zero map from the free
sheaf of modules on no generators. -/
instance isQuasicoherent_free (I : Type u) : (free (R := R) I).IsQuasicoherent :=
  (presentationOfIsCokernelFree (ι := PEmpty.{u + 1}) (0 : free _ ⟶ free (R := R) I) (𝟙 _)
    (by simp) (CokernelCofork.IsColimit.ofId _ rfl)).isQuasicoherent

/-- The unit sheaf of modules is quasi-coherent. -/
instance isQuasicoherent_unit : (unit R).IsQuasicoherent :=
  (isQuasicoherent R).prop_of_iso (freeUniqueIso PUnit.{u + 1}) (isQuasicoherent_free _)

end SheafOfModules
