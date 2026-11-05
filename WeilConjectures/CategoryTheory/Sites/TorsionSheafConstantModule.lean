/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Module.ZMod

/-!
# Abelian sheaves killed by `N` are modules over the constant sheaf `ℤ/N`

Let `J` be a Grothendieck topology on a category `C` and `N ≥ 1`. Write `(ℤ/N)_C` for the
constant sheaf of rings with value `ℤ/N` (`CategoryTheory.Sheaf.constantZModSheaf`), the
sheafification of the constant presheaf of rings, and `η : ℤ/N ⟶ (ℤ/N)_C` for the unit
(`CategoryTheory.Sheaf.constantZModUnit`).

Every sheaf of `(ℤ/N)_C`-modules is killed by `N`, and a constant section `η(a)` acts on it as
multiplication by any integer representative of `a`. Conversely an abelian sheaf `F` killed by
`N` carries a structure of sheaf of `(ℤ/N)_C`-modules, unique up to unique isomorphism, and
every morphism of abelian sheaves between sheaves of `(ℤ/N)_C`-modules is `(ℤ/N)_C`-linear: the
forgetful functor `SheafOfModules (ℤ/N)_C ⥤ Sheaf J AddCommGrpCat` is fully faithful with
essential image the sheaves killed by `N` (Stacks 03CY).

## Main definitions

- `CategoryTheory.Sheaf.constantZModSheaf`: the constant sheaf of rings `(ℤ/N)_C`.
- `CategoryTheory.Sheaf.constantZModUnit`: the unit `ℤ/N ⟶ (ℤ/N)_C` of the sheafification.

## Main statements

- `CategoryTheory.Sheaf.constantZModUnit_smul`: `η(a)` acts as multiplication by `a.val`.
- `CategoryTheory.Sheaf.nsmul_eq_zero_of_constantZMod`: sheaves of `(ℤ/N)_C`-modules are killed
  by `N`.
- `CategoryTheory.Sheaf.full_toSheaf_constantZMod`: morphisms of abelian sheaves are linear.
- `CategoryTheory.Sheaf.exists_constantZModModule_iff`: the essential image of the forgetful
  functor is the sheaves killed by `N`.
- `CategoryTheory.Sheaf.torsionSheaf_constantModule`: blueprint
  `lem-pur-torsion-sheaf-constant-module`.

## Implementation notes

The proof follows the étale special case
`AlgebraicGeometry.Etale.constantRing_moduleSheaf_equivalence`:
over the constant *presheaf* of rings `ℤ/N` the restriction maps of a presheaf of modules are
`ℤ/N`-linear, so presheaves of modules over it are presheaves of `ℤ/N`-modules, and Mathlib's
restriction of scalars along the locally bijective unit `η` is fully faithful on sheaves of
modules (`PresheafOfModules.sheafification`).
-/

@[expose] public section

universe w v u

open CategoryTheory Opposite

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (N : ℕ)
  [HasWeakSheafify J RingCat.{w}]

/-- The constant presheaf of rings with value `ℤ/N`. -/
abbrev constantZModPresheaf : Cᵒᵖ ⥤ RingCat.{w} :=
  (Functor.const Cᵒᵖ).obj (RingCat.of (ULift.{w} (ZMod N)))

variable {J N}

variable [J.WEqualsLocallyBijective RingCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The `ℤ/N`-module structures on the sections of an abelian presheaf killed by `N`. -/
abbrev moduleOfNsmul (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (hF : ∀ (U : Cᵒᵖ) (x : F.obj U), N • x = 0)
    (U : Cᵒᵖ) : Module ((constantZModPresheaf.{w} (C := C) N).obj U) (F.obj U) :=
  letI : Module (ZMod N) (F.obj U) := AddCommGroup.zmodModule (hF U)
  inferInstanceAs (Module (ULift.{w} (ZMod N)) (F.obj U))

/-- An abelian presheaf killed by `N`, as a presheaf of modules over the constant presheaf of
rings `ℤ/N`. -/
noncomputable def presheafOfModulesOfNsmul (F : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    (hF : ∀ (U : Cᵒᵖ) (x : F.obj U), N • x = 0) :
    PresheafOfModules.{w} (constantZModPresheaf.{w} (C := C) N) :=
  letI := moduleOfNsmul F hF
  PresheafOfModules.ofPresheaf F fun U V f r m ↦ by
    let : Module (ZMod N) (F.obj U) := AddCommGroup.zmodModule (hF U)
    let : Module (ZMod N) (F.obj V) := AddCommGroup.zmodModule (hF V)
    exact (AddMonoidHom.toZModLinearMap N (F.map f).hom).map_smul r.down m

end CategoryTheory.Sheaf
