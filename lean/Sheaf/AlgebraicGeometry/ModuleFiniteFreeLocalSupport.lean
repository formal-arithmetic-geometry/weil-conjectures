/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Sheaf.AlgebraicGeometry.ModuleStalkFilteredColimit

/-! # Finite support of finite free maps

Source: Stacks Project, Modules, Tags 01BB and 01AH.
(blueprint: lem-weil-pbc-module-finite-free-local-support).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- A map from a finite free sheaf into a restricted free sheaf has finite basis
support on a neighbourhood of any given point.

Source: Stacks Project, Modules, proof of Lemma 01BB and Lemma 01AH.
(blueprint: lem-weil-pbc-module-finite-free-local-support).

Proof: Evaluate the images of the finitely many basis sections at the point.
The free sheaf is the filtered colimit of its finite sub-coproducts, and taking
stalks preserves this colimit. Thus each image germ lies in a finite sub-coproduct.
Take the union S of these finitely many supports. Each resulting lift germ is
represented by a section of the finite sub-coproduct near the point; equality of
its image and the original basis section holds after shrinking. Intersect the
finitely many neighbourhoods to get W. The lifted basis sections define a map a.
Both composites agree on every basis section, so the universal property of the
finite free sheaf gives the displayed morphism equality. Restriction preserves
free sheaves, coprojections and their basis maps. For n = 0 choose W = U and
S empty; the map out of the zero object is unique. For an empty index type I
the target free sheaf is zero and the same choice of S works. No finite type
or surjectivity assumption is used. -/
theorem exists_finite_free_local_support
    (X : Scheme.{u}) (V U : X.Opens) (hUV : U ≤ V)
    (I : Type u) (n : ℕ)
    (l : free (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin n)) ⟶
      (overMap (moduleRings X.toRingedSpace) (homOfLE hUV)).obj
        (free (R := (moduleRings X.toRingedSpace).over V) I)) (x : U) :
    ∃ (W : X.Opens) (hWU : W ≤ U), (x : X) ∈ W ∧ ∃ (S : Finset I)
      (a : (overMap (moduleRings X.toRingedSpace) (homOfLE hWU)).obj
          (free (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin n))) ⟶
        (overMap (moduleRings X.toRingedSpace) (homOfLE (hWU.trans hUV))).obj
          (free (R := (moduleRings X.toRingedSpace).over V) S)),
      a ≫ (overMap (moduleRings X.toRingedSpace) (homOfLE (hWU.trans hUV))).map
        (freeMap (R := (moduleRings X.toRingedSpace).over V) ((↑) : S → I)) =
      (overMap (moduleRings X.toRingedSpace) (homOfLE hWU)).map l := by sorry

end AlgebraicGeometry.Scheme.Modules
