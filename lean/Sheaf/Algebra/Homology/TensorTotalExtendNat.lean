/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import WeilConjectures.Mathlib.Algebra.Homology.ComplexShapeSigns

/-! # Tensor totalization and extension by zero

Source: Stacks Project, Tag 012Z, the diagonal direct-sum total formula.
(blueprint: lem-sc-tensor-total-extend-nat).
-/

@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace HomologicalComplex

/-- Zero extension commutes with tensor totalization, preserving summand inclusions.
Source: Stacks Project, Tag 012Z, the diagonal direct-sum total formula.
(blueprint: lem-sc-tensor-total-extend-nat).

Proof: In total degree n>=0 only summands with two nonnegative indices survive.
The map sends each integer summand (p,q) to the natural summand (p.toNat,q.toNat)
using the two extendXIso homomorphisms. Its inverse sends each natural summand
back using their inverses. A negative factor is zero, so its tensor summand is
zero and has a unique map. The coproduct universal property defines both maps.
Checking on each coprojection proves that they are inverse. In negative total
degree all summands have a negative factor, and both complexes are zero there.
For consecutive nonnegative degrees check differential compatibility on each
summand: the two tensor differential terms become the same factor differentials
under extend_d_eq, and (-1)^p agrees with the integer sign at the cast of p.
The boundary from -1 to 0 has zero source. All other differentials vanish by
shape. These degree maps define a cochain isomorphism; its construction gives
the displayed summand identity. Degree zero has only the (0,0) summand; zero
factor complexes have only zero summands, so both cases obey the same formula. -/
theorem tensorTotal_extend_nat
    {k : Type w} [Field k] (A B : CochainComplex (ModuleCat.{w} k) ℕ) :
    ∃ s : mapBifunctor (A.extend ComplexShape.embeddingUpNat)
        (B.extend ComplexShape.embeddingUpNat) (curriedTensor (ModuleCat.{w} k))
          (ComplexShape.up ℤ) ≅
      (mapBifunctor A B (curriedTensor (ModuleCat.{w} k))
        (ComplexShape.up ℕ)).extend ComplexShape.embeddingUpNat,
      ∀ p q : ℕ,
        ιMapBifunctor (A.extend ComplexShape.embeddingUpNat)
            (B.extend ComplexShape.embeddingUpNat) (curriedTensor (ModuleCat.{w} k))
              (ComplexShape.up ℤ) (p : ℤ) (q : ℤ) ((p + q : ℕ) : ℤ)
                (by change (p : ℤ) + (q : ℤ) = ((p + q : ℕ) : ℤ); omega) ≫
          s.hom.f ((p + q : ℕ) : ℤ) ≫
          ((mapBifunctor A B (curriedTensor (ModuleCat.{w} k))
            (ComplexShape.up ℕ)).extendXIso ComplexShape.embeddingUpNat
              (i := p + q) rfl).hom =
        ((A.extendXIso ComplexShape.embeddingUpNat (i := p) rfl).hom ⊗ₘ
          (B.extendXIso ComplexShape.embeddingUpNat (i := q) rfl).hom) ≫
          ιMapBifunctor A B (curriedTensor (ModuleCat.{w} k))
            (ComplexShape.up ℕ) p q (p + q) rfl := by sorry

end HomologicalComplex
