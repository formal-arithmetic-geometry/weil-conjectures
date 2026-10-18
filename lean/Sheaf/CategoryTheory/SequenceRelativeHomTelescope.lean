/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q156
-/
module

public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Hom into a sequence-relative telescope

Source: Stacks Project, Derived Categories, Tags 0CRK, 094A and 093W; the
sequence-relative version of their exact-sequence argument
(blueprint: lem-weil-pbc-sequence-relative-hom-telescope).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite DirectSum

namespace CategoryTheory

/-- Hom into a chosen telescope is the sequential colimit of the Hom groups if the
coproduct comparisons for this sequence and its shift by one are bijective.
Source: Stacks Project, Derived Categories, Tags 0CRK, 094A and 093W
(blueprint: lem-weil-pbc-sequence-relative-hom-telescope).

The colimit is in `AddCommGrpCat`; its transitions are postcomposition with the maps
of `X`. The equations on every stage uniquely specify the canonical group homomorphism.
Only the supplied coproduct and the two displayed comparisons are assumed.

Proof:
1. Put `A n = Hom(K, X n)` and `A' n = Hom(K, X n[1])`. The two assumed
   bijective additive comparison maps identify their direct sums with `Hom(K, B)`
   and `Hom(K, B[1])`. On each summand, postcomposition by `1 - s` corresponds
   to identity minus the forward transition shift. The same holds after shifting,
   since shift is additive (`def-weil-triangulated-category`). These identities
   extend to finite sums.
2. Identity minus forward shift on the shifted direct sum is injective: its
   zeroth coordinate gives `g 0 = 0`, and coordinate `n + 1` gives
   `g (n + 1) = u n[1] (g n)`. Induction makes every coordinate zero.
   Transport through the shifted comparison to obtain injectivity of `(1 - s)[1]_*`.
3. Apply `lem-weil-pbc-hom-into-triangle-exact` to the triangle and its rotations.
   Consecutive composites vanish, so injectivity in step 2 forces every map into
   `H` to have zero composite with `q`. Exactness of the once-rotated triangle
   makes postcomposition by `p` surjective. Exactness of the original triangle
   identifies its kernel with the image of postcomposition by `1 - s`.
   Thus the induced map from the unshifted direct sum is surjective with kernel
   the image of identity minus forward shift.
4. The quotient of that sum by this image is the sequential colimit of the
   groups `A n` (`def-weil-pbc-category-colimit`): its summand maps are compatible.
   Every compatible family of group homomorphisms extends to the sum, kills the
   image, and factors uniquely through the quotient. Successor compatibility
   extends to all transitions by induction.
5. Step 3 induces an injective and surjective homomorphism from this quotient to
   `Hom(K, H)`. Its value on a stage element is `f ≫ iota n ≫ p`.
   The colimit universal property identifies it with precisely the stated map.
   No coproduct comparison for any other family is used. -/
theorem sequence_relative_hom_telescope
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    (K : C) (X : ℕ ⥤ C) (B : C) (iota : ∀ n : ℕ, X.obj n ⟶ B)
    (hB : IsColimit (Cofan.mk B iota))
    (s : B ⟶ B)
    (hs : ∀ n : ℕ, iota n ≫ s = X.map (homOfLE (Nat.le_succ n)) ≫ iota (n + 1))
    (H : C) (p : B ⟶ H) (q : H ⟶ B⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (𝟙 B - s) p q ∈ distTriang C)
    (hcomp : Function.Bijective
      (DirectSum.toAddMonoid (fun n : ℕ ↦ Preadditive.rightComp K (iota n)) :
        (⨁ n : ℕ, (K ⟶ X.obj n)) →+ (K ⟶ B)))
    (hcompShift : Function.Bijective
      (DirectSum.toAddMonoid (fun n : ℕ ↦
        Preadditive.rightComp K ((iota n)⟦(1 : ℤ)⟧')) :
        (⨁ n : ℕ, (K ⟶ (X.obj n)⟦(1 : ℤ)⟧)) →+ (K ⟶ B⟦(1 : ℤ)⟧))) :
    ∃ phi : colimit (X ⋙ preadditiveCoyoneda.obj (op K)) ⟶ AddCommGrpCat.of (K ⟶ H),
      (∀ (n : ℕ) (f : K ⟶ X.obj n),
        phi (colimit.ι (X ⋙ preadditiveCoyoneda.obj (op K)) n f) = f ≫ iota n ≫ p) ∧
      Function.Bijective phi := by
  sorry

end CategoryTheory
