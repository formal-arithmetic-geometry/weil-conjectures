/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Scalar action calculation for an affine chart

## References

* [Stacks Project, Tag 01IB](https://stacks.math.columbia.edu/tag/01IB)
* [Stacks Project, Tag 01HV](https://stacks.math.columbia.edu/tag/01HV)
-/

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Scalar multiplication on a module induces scalar multiplication on every
section of its associated sheaf. -/
theorem tilde_scalar_section_action (R : CommRingCat.{u}) (M : ModuleCat.{u} R)
    (a : R) (f : M ⟶ M) (hf : ∀ m : M, f m = a • m)
    (V : (Spec R).Opens) (s : Γ((tilde.functor R).obj M, V)) :
    (((tilde.functor R).map f).val.app (.op V)) s = a • s := by
  apply Subtype.ext
  funext x
  dsimp [tilde.functor, tilde.map, tilde.modulesSpecToSheafIso,
    SpecModulesToSheafFullyFaithful, StructureSheaf.comapₗ, StructureSheaf.comapFun]
  change StructureSheaf.Localizations.comapFun f.hom x.1 (s.1 x) = _
  have hs : (a • s).1 x = a • s.1 x := by
    have h := (((tilde.modulesSpecToSheafIso M).app (.op V)).hom.hom).map_smul a s
    exact congrArg (fun t ↦ t.1 x) h
  rw [hs]
  generalize s.1 x = z
  induction z using LocalizedModule.induction_on with
  | _ m t =>
    simp only [StructureSheaf.Localizations.comapFun_mk, hf]
    rw [LocalizedModule.smul'_mk]
    rfl

end AlgebraicGeometry.Scheme
