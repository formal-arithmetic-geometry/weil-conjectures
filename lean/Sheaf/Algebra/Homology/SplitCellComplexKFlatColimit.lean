/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat

/-! K-flatness under exhaustive filtered unions of subcomplexes.
(blueprint: lem-kun-split-cell-complex-kflat-exhaustive-colimit)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- The inclusions and exhaustion identify C with the filtered colimit of the F m degreewise.
Tensor comparison commutes with this colimit, and exact filtered colimits preserve the equality of
cycles and boundaries. Thus tensoring any acyclic complex with C is acyclic, which is K-flat.
(blueprint: lem-kun-split-cell-complex-kflat-exhaustive-colimit)
-/
theorem kFlat_of_exhaustive_split_colimit {R : Type u} [CommRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℤ)
    (F : ℕ → CochainComplex (ModuleCat.{u} R) ℤ)
    (ι : ∀ m : ℕ, F m ⟶ C)
    (step : ∀ m : ℕ, F m ⟶ F (m + 1))
    (hmono : ∀ m : ℕ, Mono (ι m))
    (hcompat : ∀ m : ℕ, step m ≫ ι (m + 1) = ι m)
    (hexhaustive : ∀ (n : ℤ) (x : C.X n),
      ∃ (m : ℕ) (y : (F m).X n), (ι m).f n y = x)
    (hstage : ∀ m : ℕ, (HomologicalComplex.quasiIso (ModuleCat.{u} R)
      (ComplexShape.up ℤ)).kFlat (F m)) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)).kFlat C := by
  sorry

end CochainComplex
