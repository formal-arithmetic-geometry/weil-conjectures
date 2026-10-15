/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Exact functors preserve sequential homotopy colimits

Source: Weil conjectures blueprint, sec-smooth-purity, sk-prop-sf-kunneth-ordinary,
node order 1721 (blueprint: lem-kun-functor-preserves-hocolim);
Stacks Project, Derived Categories, Tags 090Z, 0145, 014V and 014A.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

/-- An exact functor preserving countable coproducts carries a chosen telescope to a
homotopy colimit. For any two chosen telescope triangles, their coproduct comparison
extends to a triangle morphism, and every extension is invertible. No uniqueness of
that extension is asserted. Here `sigmaComparison F E` is the canonical arrow from
`∐ (fun n ↦ F.obj (E n))` to `F.obj (∐ E)`, and `(F.commShiftIso 1).hom.app (∐ E)`
is the specified shift comparison.

Source: blueprint sec-smooth-purity, sk-prop-sf-kunneth-ordinary, node order 1721;
Stacks Project, Tags 090Z, 0145, 014V and 014A
(blueprint: lem-kun-functor-preserves-hocolim).

Proof:
1. Use the telescope definition (def-kun-truncations) and TR1
   (def-weil-triangulated-category) to fix the two distinguished triangles.
2. The coproduct universal property (def-weil-pbc-category-colimit) constructs the
   comparison alpha and its inverse, because F preserves the coproduct. Their
   composites restrict to identities on every coprojection, hence are identities.
3. Compute on coprojections that s' followed by alpha equals alpha followed by F(s).
   Additivity of the exact functor gives the corresponding square for 1-s' and F(1-s).
4. Exactness makes the image triangle distinguished, with last arrow F(q) followed
   by the specified shift comparison. TR3 completes (alpha, alpha) to c satisfying
   the two displayed squares (def-weil-triangulated-category).
5. Every such completion is invertible by the two-out-of-three theorem for triangle
   morphisms (lem-sf-triangle-morphism-iso). Transport the distinguished image triangle
   along alpha in its first two objects and the identity on F(H) in its third object.
   Its last arrow is F(q), then the shift comparison, then the inverse shifted alpha.
   The resulting triangle has first arrow 1-s', so def-kun-truncations identifies F(H)
   as a homotopy colimit. This proves existence and invertibility without uniqueness. -/
theorem Functor.preserves_sequentialHomotopyColimit
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
    [HasShift C ℤ] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    [CategoryTheory.IsTriangulated C] [CategoryTheory.IsTriangulated D]
    [HasCountableCoproducts C] [HasCountableCoproducts D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    [PreservesColimitsOfShape (Discrete ℕ) F]
    (E : ℕ → C) (u : ∀ n : ℕ, E n ⟶ E (n + 1)) (H : C) (H' : D)
    (p : (∐ E) ⟶ H) (q : H ⟶ (∐ E)⟦(1 : ℤ)⟧)
    (p' : (∐ fun n : ℕ ↦ F.obj (E n)) ⟶ H')
    (q' : H' ⟶ (∐ fun n : ℕ ↦ F.obj (E n))⟦(1 : ℤ)⟧)
    (hT : Triangle.mk
      (𝟙 (∐ E) - Sigma.desc (fun n : ℕ ↦ u n ≫ Sigma.ι E (n + 1))) p q ∈ distTriang C)
    (hT' : Triangle.mk
      (𝟙 (∐ fun n : ℕ ↦ F.obj (E n)) -
        Sigma.desc (fun n : ℕ ↦ F.map (u n) ≫
          Sigma.ι (fun k : ℕ ↦ F.obj (E k)) (n + 1))) p' q' ∈ distTriang D) :
    IsIso (sigmaComparison F E) ∧
    (∃ c : H' ⟶ F.obj H,
      p' ≫ c = sigmaComparison F E ≫ F.map p ∧
      c ≫ F.map q ≫ (F.commShiftIso (1 : ℤ)).hom.app (∐ E) =
        q' ≫ (shiftFunctor D (1 : ℤ)).map (sigmaComparison F E)) ∧
    (∀ c : H' ⟶ F.obj H,
      p' ≫ c = sigmaComparison F E ≫ F.map p →
      c ≫ F.map q ≫ (F.commShiftIso (1 : ℤ)).hom.app (∐ E) =
        q' ≫ (shiftFunctor D (1 : ℤ)).map (sigmaComparison F E) → IsIso c) ∧
    IsSequentialHomotopyColimit (fun n : ℕ ↦ F.obj (E n))
      (fun n : ℕ ↦ F.map (u n)) (F.obj H) := by
  sorry

end CategoryTheory
