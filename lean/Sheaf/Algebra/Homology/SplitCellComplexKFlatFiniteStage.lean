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
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat

/-! Finite-stage K-flatness for split free-cell filtrations.
(blueprint: lem-kun-split-cell-complex-kflat-finite-stage)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Finite-stage induction: the zero stage is K-flat. A degreewise retraction splits the tensor
short exact sequence at each successor; the zero-differential free quotient tensors every acyclic
complex to an acyclic direct sum. The long exact homology sequence then gives K-flatness of the
successor. (blueprint: lem-kun-split-cell-complex-kflat-finite-stage)
-/
theorem kFlat_of_split_free_cells_finite_stage {R : Type u} [CommRing R]
    (F : ℕ → CochainComplex (ModuleCat.{u} R) ℤ)
    (step : ∀ m : ℕ, F m ⟶ F (m + 1))
    (hzero : IsZero (F 0))
    (hsplit : ∀ (m : ℕ) (n : ℤ),
      ∃ r : (F (m + 1)).X n ⟶ (F m).X n,
        (step m).f n ≫ r = 𝟙 ((F m).X n))
    (hquot_d : ∀ (m : ℕ) (n : ℤ), (cokernel (step m)).d n (n + 1) = 0)
    (hquot_free : ∀ (m : ℕ) (n : ℤ),
      Module.Free R ((cokernel (step m)).X n)) :
    ∀ m : ℕ, (HomologicalComplex.quasiIso (ModuleCat.{u} R)
      (ComplexShape.up ℤ)).kFlat (F m) := by
  sorry

end CochainComplex
