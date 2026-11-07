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

/-- The constant sheaf of rings `(ℤ/N)_C`: the sheafification of the constant presheaf of
rings with value `ℤ/N`. -/
noncomputable abbrev constantZModSheaf : Sheaf J RingCat.{w} :=
  (constantSheaf J RingCat.{w}).obj (RingCat.of (ULift.{w} (ZMod N)))

/-- The unit `ℤ/N ⟶ (ℤ/N)_C` of the sheafification of the constant presheaf of rings. -/
noncomputable abbrev constantZModUnit : constantZModPresheaf N ⟶ (constantZModSheaf J N).obj :=
  toSheafify J (constantZModPresheaf N)

variable {J N}

/-- A constant section `η(a)` of `(ℤ/N)_C`, `a ∈ ℤ/N`, acts on a sheaf of `(ℤ/N)_C`-modules as
multiplication by the integer representative `a.val` of `a` (or any other one, since the sheaf
is killed by `N`: `CategoryTheory.Sheaf.nsmul_eq_zero_of_constantZMod`). -/
lemma constantZModUnit_smul [NeZero N] (M : SheafOfModules.{w} (constantZModSheaf J N))
    {U : Cᵒᵖ} (a : ZMod N) (x : M.val.obj U) :
    (constantZModUnit J N).app U ⟨a⟩ • x = a.val • x := by
  have : (⟨a⟩ : ULift.{w} (ZMod N)) = (a.val : ULift.{w} (ZMod N)) :=
    ULift.ext (by rw [ULift.down_natCast, ZMod.natCast_zmod_val])
  rw [this, map_natCast, Nat.cast_smul_eq_nsmul]


variable [J.WEqualsLocallyBijective RingCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The morphism of presheaves of modules over the constant presheaf `ℤ/N` underlying a
morphism of abelian sheaves between sheaves of `(ℤ/N)_C`-modules: additive maps between
`ℤ/N`-modules are `ℤ/N`-linear. -/
noncomputable def restrictScalarsHomOfToSheaf [NeZero N]
    {M M' : SheafOfModules.{w} (constantZModSheaf J N)}
    (φ : (SheafOfModules.toSheaf _).obj M ⟶ (SheafOfModules.toSheaf _).obj M') :
    (PresheafOfModules.restrictScalars (constantZModUnit J N)).obj M.val ⟶
      (PresheafOfModules.restrictScalars (constantZModUnit J N)).obj M'.val :=
  PresheafOfModules.homMk φ.hom fun U r m ↦ by
    obtain ⟨a⟩ := r
    have key : ∀ y : M.val.obj U, φ.hom.app U ((constantZModUnit J N).app U ⟨a⟩ • y) =
        (constantZModUnit J N).app U ⟨a⟩ • (show M'.val.obj U from φ.hom.app U y) := fun y ↦ by
      rw [constantZModUnit_smul, constantZModUnit_smul]
      exact map_nsmul (φ.hom.app U).hom _ _
    exact key m

/-- Every morphism of abelian sheaves between sheaves of `(ℤ/N)_C`-modules is
`(ℤ/N)_C`-linear: the forgetful functor to abelian sheaves is full. -/
instance full_toSheaf_constantZMod [NeZero N] :
    (SheafOfModules.toSheaf.{w} (constantZModSheaf J N)).Full where
  map_surjective {M M'} φ := by
    obtain ⟨χ, hχ⟩ := (SheafOfModules.forget.{w} (constantZModSheaf J N) ⋙
      PresheafOfModules.restrictScalars (constantZModUnit J N)).map_surjective
        (restrictScalarsHomOfToSheaf φ)
    exact ⟨χ, ObjectProperty.hom_ext _ (congrArg (PresheafOfModules.toPresheaf _).map hχ)⟩

/-- The forgetful functor from sheaves of `(ℤ/N)_C`-modules to abelian sheaves is fully
faithful. -/
noncomputable def fullyFaithfulToSheafConstantZMod [NeZero N] :
    (SheafOfModules.toSheaf.{w} (constantZModSheaf J N)).FullyFaithful :=
  .ofFullyFaithful _

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

/-- The sheaf of `(ℤ/N)_C`-modules on an abelian sheaf `F` killed by `N`: the sheafification
of the presheaf of `ℤ/N`-modules `F`. -/
noncomputable def constantZModModuleOfNsmul (F : Sheaf J AddCommGrpCat.{w})
    (hF : ∀ (U : Cᵒᵖ) (x : F.obj.obj U), N • x = 0) :
    SheafOfModules.{w} (constantZModSheaf J N) :=
  (PresheafOfModules.sheafification.{w} (constantZModUnit J N)).obj
    (presheafOfModulesOfNsmul F.obj hF)

/-- The underlying abelian sheaf of `CategoryTheory.Sheaf.constantZModModuleOfNsmul F hF` is
`F`: the sheafification of the sheaf `F` is `F`. -/
noncomputable def toSheafConstantZModModuleOfNsmulIso (F : Sheaf J AddCommGrpCat.{w})
    (hF : ∀ (U : Cᵒᵖ) (x : F.obj.obj U), N • x = 0) :
    (SheafOfModules.toSheaf _).obj (constantZModModuleOfNsmul F hF) ≅ F :=
  (PresheafOfModules.sheafificationCompToSheaf (constantZModUnit J N)).app
    (presheafOfModulesOfNsmul F.obj hF) ≪≫ (sheafificationIso F).symm


end CategoryTheory.Sheaf
