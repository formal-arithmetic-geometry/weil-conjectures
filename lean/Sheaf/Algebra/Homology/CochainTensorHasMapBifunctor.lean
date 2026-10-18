/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Mathlib.Algebra.Homology.Bifunctor

/-!
# Existence of total tensor products of cochain complexes
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Cochain bifunctor totals exist when all small coproducts exist.
Source: Mathlib, `HomologicalComplex.HasMapBifunctor`, and the coproduct instance
for total complexes (blueprint: lem-weil-pbc-cochain-tensor-has-map-bifunctor).
Proof: for each total degree, take the coproduct over pairs of integers with the
specified sum. These index types are small; the assumed coproducts therefore
supply exactly the total-complex existence instance. Mathlib constructs it. -/
theorem cochainTensorHasMapBifunctor
    {A : Type u} [Category.{v} A] [HasZeroMorphisms A]
    {B : Type u} [Category.{v} B] [HasZeroMorphisms B]
    {D : Type u} [Category.{v} D] [Preadditive D] [HasCoproducts.{0} D]
    (T : A ⥤ B ⥤ D) [T.PreservesZeroMorphisms]
    [∀ X, (T.obj X).PreservesZeroMorphisms]
    (P : CochainComplex A ℤ) (Q : CochainComplex B ℤ) :
    HomologicalComplex.HasMapBifunctor P Q T (ComplexShape.up ℤ) :=
  inferInstance

end CategoryTheory
