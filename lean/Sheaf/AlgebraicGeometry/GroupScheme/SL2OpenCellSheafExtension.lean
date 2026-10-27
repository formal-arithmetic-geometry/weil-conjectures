/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Extension from the open cell of SL₂ to an arbitrary group sheaf

Source: Conrad, Reductive group schemes, Proposition 4.3.1, final paragraphs,
printed pp. 130–131, especially (4.3.2).
(blueprint: lem-sfb-sl2-open-cell-sheaf-extension)

The open cell is expressed directly by the unit condition on the bottom-right entry.
A natural map on it is a family with an explicit naturality equation; a group-sheaf
homomorphism is a natural family of group homomorphisms. Thus no representability,
separatedness, or commutativity condition is imposed on the target sheaf.
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- A partially multiplicative natural map on the SL₂ open cell extends uniquely to
a homomorphism into any fppf sheaf of groups.

Source: Conrad, Reductive group schemes, Proposition 4.3.1, printed pp. 130–131,
finite-word comparison (4.3.2).
(blueprint: lem-sfb-sl2-open-cell-sheaf-extension)

Proof:
1. On each affine open, det(gᵢ) = 1 makes the pairs (bᵢ,dᵢ) unimodular.
   Apply lem-sfb-unimodular-linear-forms-fppf-cover to find fppf-locally z such
   that every bᵢz+dᵢ is a unit. The element ω = y(z), its inverse, and all ωgᵢ
   then lie in the open cell. In particular every g is locally a two-letter word.
2. For two equal finite open-cell words, apply this simultaneously to all their
   prefix products. Partial multiplicativity inductively identifies each translated
   prefix value with σ(ω) times the product of the letter values. Cancel σ(ω).
   The separatedness part of the sheaf axiom descends the equality, including for
   empty words, using σ(1) = 1.
3. Evaluate local two-letter words using σ. Word comparison identifies their values
   on overlaps, so the sheaf axiom glues a unique section. Comparing choices proves
   independence; pulling back the local words proves naturality. Comparison with a
   one-letter word gives the required restriction to the open cell.
4. Concatenating words proves preservation of multiplication. The empty word gives
   preservation of identity, and applying multiplication to g and g⁻¹ gives inverses.
   Any other homomorphism extending σ has the same values on the local words, hence
   equals this one by the uniqueness of gluing. -/
theorem existsUnique_sl2_openCell_extension
    (S : Scheme.{u}) (H : Sheaf (Scheme.fppfTopology.over S) GrpCat.{v})
    (σ : ∀ (T : Over S) (g : Matrix.SpecialLinearGroup (Fin 2) Γ(T.left, ⊤)),
      IsUnit (g 1 1) → H.obj.obj (op T))
    (hσ_natural : ∀ (T U : Over S) (f : U ⟶ T)
      (g : Matrix.SpecialLinearGroup (Fin 2) Γ(T.left, ⊤)) (hg : IsUnit (g 1 1)),
      H.obj.map f.op (σ T g hg) =
        σ U (Matrix.SpecialLinearGroup.map f.left.appTop.hom g)
          (hg.map f.left.appTop.hom))
    (hσ_one : ∀ T : Over S, σ T 1 isUnit_one = 1)
    (hσ_mul : ∀ (T : Over S) (a b : Matrix.SpecialLinearGroup (Fin 2) Γ(T.left, ⊤))
      (ha : IsUnit (a 1 1)) (hb : IsUnit (b 1 1)) (hab : IsUnit ((a * b) 1 1)),
      σ T a ha * σ T b hb = σ T (a * b) hab) :
    ∃! τ : ∀ T : Over S,
        Matrix.SpecialLinearGroup (Fin 2) Γ(T.left, ⊤) →* H.obj.obj (op T),
      (∀ (T U : Over S) (f : U ⟶ T)
        (g : Matrix.SpecialLinearGroup (Fin 2) Γ(T.left, ⊤)),
        H.obj.map f.op (τ T g) =
          τ U (Matrix.SpecialLinearGroup.map f.left.appTop.hom g)) ∧
      (∀ (T : Over S) (g : Matrix.SpecialLinearGroup (Fin 2) Γ(T.left, ⊤))
        (hg : IsUnit (g 1 1)), τ T g = σ T g hg) := by
  sorry

end AlgebraicGeometry
