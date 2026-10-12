/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits

import Sheaf.Algebra.Homology.FreeComplexCover

/-!
# An exact bicomplex of free two-step covers

Source: Stacks Project, Tag 09KP, construction of the resolution and total augmentation.
(blueprint: lem-pc-derived-free-cover-bicomplex)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Iteration of the free-complex cover, followed by direct-sum totalization.
Source: Stacks Project, Differential Graded Algebra, Tag 09KP, proof, construction
of the resolution and its augmentation (using Tag 09KN).
(blueprint: lem-pc-derived-free-cover-bicomplex)

Proof. Starting at `N₀ = M`, choose the cover `Pᵢ → Nᵢ` of Tag 09KN and set
`Nᵢ₊₁` equal to its kernel. Define `Pᵢ₊₁ → Pᵢ` as the cover of `Nᵢ₊₁` followed
by the kernel inclusion. These maps compose to zero. They are exact in each
module degree since the covers are surjective and their kernels are the chosen
`Nᵢ₊₁`. They are also exact on cycles: a cycle mapping to zero factors uniquely
through the kernel complex, is a cycle there since its inclusion is injective,
and lifts to a cycle of the next cover by the cocycle-surjectivity clause of 09KN.
The same argument proves exactness at `P₀`, and 09KN gives surjectivity of both
augmented rows at `M`.

Put `Pᵢ` in column `-i`, and zero in positive columns. The horizontal maps are
the maps just constructed; they commute with the vertical differentials because
they are maps of complexes. This gives `K`. Module categories have the direct
sums defining its total complex. On each diagonal define the augmentation by
the cover `P₀ → M` on column zero and zero on negative columns. The horizontal
boundary from column `-1` is killed by this cover; in column zero the vertical
sign is one. Thus these component maps commute with differentials and give `ε`.
Finally retain the split short exact sequence and the two free graded pieces
provided by 09KN for each `Pᵢ`; their middle objects identify with `K.X (-i)`.
-/
theorem exists_freeCoverBicomplex {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    ∃ K : HomologicalComplex₂ (ModuleCat.{u} A) (ComplexShape.up ℤ) (ComplexShape.up ℤ),
      ∃ (ε : K.total (ComplexShape.up ℤ) ⟶ M) (a : K.X 0 ⟶ M),
        (∀ p : ℤ, 0 < p → IsZero (K.X p)) ∧
        (∀ q : ℤ, K.ιTotal (ComplexShape.up ℤ) 0 q q (by simp) ≫ ε.f q = a.f q) ∧
        (∀ (p q n : ℤ) (hp : p < 0)
          (h : ComplexShape.π (ComplexShape.up ℤ)
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n),
          K.ιTotal (ComplexShape.up ℤ) p q n h ≫ ε.f n = 0) ∧
        (∀ (p q : ℤ), p < -1 →
          Function.Exact ((K.d p (p + 1)).f q).hom ((K.d (p + 1) (p + 2)).f q).hom) ∧
        (∀ q : ℤ, Function.Exact ((K.d (-1) 0).f q).hom (a.f q).hom) ∧
        (∀ q : ℤ, Function.Surjective (a.f q).hom) ∧
        (∀ (p q : ℤ), p < -1 →
          Function.Exact (HomologicalComplex.cyclesMap (K.d p (p + 1)) q).hom
            (HomologicalComplex.cyclesMap (K.d (p + 1) (p + 2)) q).hom) ∧
        (∀ q : ℤ, Function.Exact (HomologicalComplex.cyclesMap (K.d (-1) 0) q).hom
          (HomologicalComplex.cyclesMap a q).hom) ∧
        (∀ q : ℤ, Function.Surjective (HomologicalComplex.cyclesMap a q).hom) ∧
        (∀ p : ℤ, p ≤ 0 →
      ∃ S : ShortComplex (CochainComplex (ModuleCat.{u} A) ℤ),
        Nonempty (S.X₂ ≅ K.X p) ∧ S.ShortExact ∧
        (∀ k : ℤ,
          Nonempty
            (S.map (HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ) k)).Splitting) ∧
        ∃ (I₁ I₃ : Type u) (d₁ : I₁ → ℤ) (d₃ : I₃ → ℤ),
          Nonempty (S.X₁ ≅ ∐ (fun i : I₁ ↦
            (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) (d₁ i)).obj
              (ModuleCat.of A A))) ∧
          Nonempty (S.X₃ ≅ ∐ (fun i : I₃ ↦
            (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) (d₃ i)).obj
              (ModuleCat.of A A)))) := by sorry

end CochainComplex
