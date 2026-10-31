/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.TruncationsAndHomotopyColimits
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
  let s := Sigma.desc (fun n : ℕ ↦ u n ≫ Sigma.ι E (n + 1))
  let E' := fun n : ℕ ↦ F.obj (E n)
  let s' := Sigma.desc (fun n : ℕ ↦ F.map (u n) ≫ Sigma.ι E' (n + 1))
  let a := sigmaComparison F E
  have ha : IsIso a := inferInstance
  have hs : s' ≫ a = a ≫ F.map s := by
    apply Sigma.hom_ext
    intro n
    dsimp only [s, s', a, E']
    simp only [Category.assoc, Sigma.ι_desc_assoc, ι_comp_sigmaComparison_assoc,
      ι_comp_sigmaComparison, ← F.map_comp, Sigma.ι_desc]
  have hfirst : (𝟙 (∐ E') - s') ≫ a = a ≫ F.map (𝟙 (∐ E) - s) := by
    rw [F.map_sub, F.map_id, Preadditive.sub_comp, Preadditive.comp_sub,
      Category.id_comp, Category.comp_id, hs]
  let T := Triangle.mk (𝟙 (∐ E) - s) p q
  let T' := Triangle.mk (𝟙 (∐ E') - s') p' q'
  have hTF : F.mapTriangle.obj T ∈ distTriang D := F.map_distinguished T hT
  obtain ⟨c, hc₂, hc₃⟩ := complete_distinguished_triangle_morphism
    T' (F.mapTriangle.obj T) hT' hTF a a hfirst
  have hc₂' : p' ≫ c = a ≫ F.map p := hc₂
  have hc₃' : c ≫ F.map q ≫ (F.commShiftIso (1 : ℤ)).hom.app (∐ E) =
      q' ≫ (shiftFunctor D (1 : ℤ)).map a := hc₃.symm
  refine ⟨ha, ⟨c, hc₂', hc₃'⟩, ?_, ?_⟩
  · intro c hc₂ hc₃
    let φ : T' ⟶ F.mapTriangle.obj T :=
      { hom₁ := a
        hom₂ := a
        hom₃ := c
        comm₁ := hfirst
        comm₂ := hc₂
        comm₃ := hc₃.symm }
    exact isIso₃_of_isIso₁₂ φ hT' hTF ha ha
  · let g := a ≫ F.map p
    let h := F.map q ≫ (F.commShiftIso (1 : ℤ)).hom.app (∐ E) ≫
      CategoryTheory.inv ((shiftFunctor D (1 : ℤ)).map a)
    let U := Triangle.mk (𝟙 (∐ E') - s') g h
    refine ⟨g, h, ?_⟩
    exact isomorphic_distinguished _ hTF U
      (Triangle.isoMk U (F.mapTriangle.obj T) (asIso a) (asIso a) (Iso.refl _)
        hfirst (by dsimp [U, g, T, Functor.mapTriangle, Triangle.mk]; simp)
        (by dsimp [U, h, T, Functor.mapTriangle, Triangle.mk]; simp))

end CategoryTheory
