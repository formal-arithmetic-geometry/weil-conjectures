/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-!
# Unbounded acyclic-complex computation in finite cohomological dimension

Source: Stacks Project, Derived Categories, Tag 07K7, assertions (1)-(2), with n = d + 1
(blueprint: lem-kun-finite-cd-acyclic-complex).
-/

@[expose] public section

universe u₁ u₂ v₁ v₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- A left exact additive functor of finite cohomological dimension has an unbounded right
derived functor, computed on every complex of right acyclic objects, naturally in chain maps.
Source: Stacks Project, Derived Categories, Tag 07K7, assertions (1)-(2)
(blueprint: lem-kun-finite-cd-acyclic-complex).

Proof plan:
1. Grothendieck abelian categories have enough injectives
   (lem-sp-grothendieck-enough-injectives). Injective objects are right acyclic
   (lem-weil-pbc-derived-functor-injective-vanishing).
2. Choose degreewise injective K-injective replacements
   (lem-pur-kinjective-degreewise-existence). Additivity makes termwise F descend to the
   homotopy category and preserve shifts and cone triangles: the canonical biproduct
   comparison preserves all four entries of the cone differential, including its minus sign.
   Apply lem-weil-pbc-kinjective-total-derived to obtain RF and its universal comparison,
   invertible on K-injectives. Pull the comparison back to complexes.
3. For an exact complex C of right acyclic terms, its cycles fit into short exact sequences
   0 → Zʳ → Cʳ → Zʳ⁺¹ → 0. The long exact sequence
   (lem-weil-pbc-derived-functor-long-exact) gives RᑫF(Zʳ⁺¹) ≅ Rᑫ⁺¹F(Zʳ) for q > 0.
   Iterating backwards d times gives RᑫF(Zʳ) ≅ Rᑫ⁺ᵈF(Zʳ⁻ᵈ) = 0.
   At d = 0 the given bound already gives the vanishing.
4. The degree-zero portion of the same long exact sequence makes
   0 → F(Zʳ) → F(Cʳ) → F(Zʳ⁺¹) → 0 exact. Left exactness identifies the first term
   with the kernel of F(dʳ); hence F(C) is exact in every degree.
5. For a quasi-isomorphism between complexes of right acyclic terms its cone is exact
   (lem-pur-quasi-iso-cone-acyclic). Its terms are right acyclic, by the split short exact
   biproduct sequences and the long exact sequence. Steps 3-4 make its image exact.
   The cone comparison of Step 2 and the cone criterion show F preserves this
   quasi-isomorphism. No boundedness or infinite-filtration convergence is used.
6. Apply Step 5 to L → I(L). Naturality compares its image with RF(Q(L → I(L))).
   These maps and the comparison at I(L) are invertible, so the comparison at L is
   invertible as well.
7. Naturality for any map L → M gives the displayed square. Since its comparison
   components are invertible on right acyclic terms, this identifies RF of the map
   with its termwise image under F, without any quasi-isomorphism assumption on the map. -/
theorem exists_rightDerived_computes_acyclic_of_finite_dimension
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [Abelian A] [IsGrothendieckAbelian.{v₁} A] [Abelian B]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (d : ℕ) (hd : ∀ (M : A) (q : ℕ), d < q → IsZero ((F.rightDerived q).obj M)) :
    ∃ (RF : DerivedCategory A ⥤ DerivedCategory B)
      (α : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
        DerivedCategory.Q ⋙ RF),
      (∀ G : DerivedCategory A ⥤ DerivedCategory B,
        Function.Bijective
          (fun β : RF ⟶ G ↦ α ≫ Functor.whiskerLeft DerivedCategory.Q β)) ∧
      (∀ L : CochainComplex A ℤ, (∀ r : ℤ, F.rightAcyclic (L.X r)) →
        IsIso (α.app L)) ∧
      (∀ (L M : CochainComplex A ℤ),
        (∀ r : ℤ, F.rightAcyclic (L.X r)) →
        (∀ r : ℤ, F.rightAcyclic (M.X r)) → ∀ f : L ⟶ M,
        DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f) ≫
          α.app M = α.app L ≫ RF.map (DerivedCategory.Q.map f)) := by
  sorry

end CategoryTheory.Functor
