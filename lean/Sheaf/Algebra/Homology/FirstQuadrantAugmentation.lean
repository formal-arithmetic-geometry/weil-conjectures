/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.QuasiIso
import Sheaf.CategoryTheory.DoubleComplexTotal

/-! # A columnwise criterion for a first-quadrant augmentation

Source: Stacks Project, Homology, Tag 0133, and Cohomology, Tag 01EQ.
-/

@[expose] public section

universe v u

open CategoryTheory

namespace HomologicalComplex₂

/-- A degree-zero augmentation of a first-quadrant bicomplex is a quasi-isomorphism
on total complexes if its augmentations of all resolution columns are quasi-isomorphisms.
Source: Stacks Project, Tag 0133 (finite diagonal argument), as used in Tag 01EQ.
(blueprint: lem-sc-first-quadrant-column-augmentation).

Proof: the cone of the total augmentation is the totalization of the augmented
columns, with the resolution degree shifted by one and the usual total signs.
Columnwise quasi-isomorphism makes all these columns acyclic. Filter by the other
(Cech) degree. In each total degree there are only finitely many summands. The first
page is zero, hence each associated graded piece of total homology is zero. Induction
on the finite filtration gives zero cone homology. Equivalently, eliminate a total
cycle's components in increasing Cech degree using column exactness; each correction
moves one step right and one step down, and the lower bound terminates the chase.
The supplied component equality identifies the resulting total augmentation with b. -/
theorem quasiIso_of_column_augmentation {C : Type u} [Category.{v} C] [Abelian C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (A : CochainComplex C ℕ) (a : A ⟶ K.X 0) (ha : a ≫ K.d 0 1 = 0)
    (b : A ⟶ K.total (ComplexShape.up ℕ))
    (hb : ∀ n : ℕ, b.f n = a.f n ≫
      K.ιTotal (ComplexShape.up ℕ) 0 n n (by simp))
    (hcol : ∀ n : ℕ, QuasiIso
      ((CochainComplex.fromSingle₀Equiv (K.flip.X n) (A.X n)).symm
        ⟨a.f n, by simpa using congrArg (fun f ↦ f.f n) ha⟩)) : QuasiIso b := by
  sorry

end HomologicalComplex₂
