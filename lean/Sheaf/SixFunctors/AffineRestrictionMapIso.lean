/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Iso
public import Sheaf.SixFunctors.FiniteDualizingData

/-! # Affine restriction transport for the finite dualizing mate -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (D : FiniteFieldDatum.{u}) (X : Scheme.{u})
  [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The global dualizing mate factors through the closed-chart and affine-space
comparisons, each of which is invertible. This is the global part of the affine-chart
argument; affine restriction transports the two factors functorially.
Source: current blueprint lem-coef-finite-dualizing.proof.md, paragraphs 1--3
(blueprint: affine-restriction-map-iso). -/
theorem finiteDualizing_etaleComparison_factorization (hl : l ≠ D.p)
    {m n : ℕ} (h : n ≤ m) :
    ∃ (Z : Etale.DerivedCategoryModule (finiteDualizingCoeff l E n) X)
      (g : (Etale.scalarExtension (finiteDualizingQuotient l E h) X).obj
        (finiteDualizingEtaleTerm l E D X m) ⟶ Z)
      (k : Z ⟶ finiteDualizingEtaleTerm l E D X n),
      IsIso g ∧ IsIso k ∧
        finiteDualizingEtaleComparison l E D X h = g ≫ k := by
  sorry

end WeilConjectures
