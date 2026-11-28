/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import WeilConjectures.CategoryTheory.Monoidal.Dualizable

/-!
# Additive functors send finite free modules to dualizable objects

Let `C` be a monoidal preadditive category with binary biproducts and `F : ModuleCat R ⥤ C` an
additive functor sending the ring `R` to a dualizable object. Then `F` sends every finite free
`R`-module to a dualizable object: such a module is a finite direct sum of copies of `R`, and
dualizable objects are stable under binary biproducts.

## Main results

- `CategoryTheory.Functor.isDualizable_obj_of_free`: `F.obj M` is dualizable for every finite
  free `R`-module `M`.
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.Functor

variable {R : Type u} [CommRing R] {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasBinaryBiproducts C] (F : ModuleCat.{u} R ⥤ C) [F.Additive]

/-- An additive functor `F : ModuleCat R ⥤ C` sending `R` to a dualizable object sends the
finite free module `Rⁿ` to a dualizable object. -/
theorem isDualizable_obj_pi_fin (hF : IsDualizable (F.obj (ModuleCat.of R R))) (n : ℕ) :
    IsDualizable (F.obj (ModuleCat.of R (Fin n → R))) := by
  induction n with
  | zero => exact IsZero.isDualizable (F.map_isZero (ModuleCat.isZero_of_subsingleton _))
  | succ n ih =>
    have := preservesBinaryBiproducts_of_preservesBiproducts F
    exact (hF.biprod ih).of_iso (F.mapBiprod _ _).symm |>.of_iso <| F.mapIso <|
      ModuleCat.biprodIsoProd (ModuleCat.of R R) (ModuleCat.of R (Fin n → R)) ≪≫
        (Fin.consLinearEquiv R fun _ ↦ R).toModuleIso

/-- **Additive functors send finite free modules to dualizable objects.** An additive functor
`F : ModuleCat R ⥤ C` to a monoidal preadditive category sending `R` to a dualizable object sends
every finite free `R`-module to a dualizable object. -/
theorem isDualizable_obj_of_free (hF : IsDualizable (F.obj (ModuleCat.of R R)))
    (M : ModuleCat.{u} R) [Module.Free R M] [Module.Finite R M] : IsDualizable (F.obj M) :=
  (F.isDualizable_obj_pi_fin hF _).of_iso <| F.mapIso <| LinearEquiv.toModuleIso <|
    ((Module.Free.chooseBasis R M).equivFun.trans
      (LinearEquiv.funCongrLeft R R (Fintype.equivFin _).symm)).symm

end CategoryTheory.Functor
