/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Extension of morphisms between distinguished triangles

Source: Beilinson–Bernstein–Deligne, *Faisceaux pervers*, Proposition 1.1.9
and Corollaire 1.1.10 (ii), pp. 23–24
(blueprint: lem-weil-pbc-triangle-morphism-extension).

## Main statements

- `triangle_morphism_extension` gives the extension, its equivalent square
  conditions, and the uniqueness assertions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

namespace CategoryTheory.Pretriangulated

/--
Source: Beilinson–Bernstein–Deligne, *Faisceaux pervers*, Proposition 1.1.9
and Corollaire 1.1.10 (ii), pp. 23–24
(blueprint: lem-weil-pbc-triangle-morphism-extension).

Proof:
1. If `T.mor₁ ≫ g ≫ T'.mor₂ = 0`, exactness of Hom into `T'` gives `f`
   completing the first square (`lem-weil-pbc-hom-into-triangle-exact`, ii).
2. TR3 (`def-weil-triangulated-category`) completes `(f,g)` to a triangle morphism.
3. A triangle morphism supplies both squares (`def-weil-pbc-triangles-with-shift`).
   Conversely, the first square implies the vanishing composite because the first
   two arrows of `T'` compose to zero (`lem-weil-pbc-hom-into-triangle-exact`, i).
4. Exactness of Hom out of `T` supplies `h` completing the second square
   (`lem-weil-pbc-hom-out-of-triangle-exact`, i).
5. TR3 for the second square supplies `f` (`lem-weil-pbc-tr3-second-square`).
   The second square also implies the vanishing composite since the first two
   arrows of `T` compose to zero (`lem-weil-pbc-hom-into-triangle-exact`, i).
6. For two first-square solutions, subtract them and shift. Exactness of Hom into
   `T'` factors their shifted difference through a map `T.obj₁[1] → T'.obj₃`
   (`lem-weil-pbc-hom-into-triangle-exact`, iii). Hom vanishing kills that map;
   faithfulness of the shift kills the original difference.
7. For two second-square solutions, exactness of Hom out of `T` factors their
   difference through `T.mor₃` and a map `T.obj₁[1] → T'.obj₃`
   (`lem-weil-pbc-hom-out-of-triangle-exact`, ii). Hom vanishing kills it.
8. Complete any first-square solution by TR3; uniqueness from step 7 identifies
   its last component with any prescribed second-square solution. The resulting
   triangle morphism has the required third square.
9. Apply step 8 to `T` and the triangle with the same first two arrows and third
   arrow `x`, using identity first and middle and last components. The third
   square gives `x = T.mor₃`; `T.mor₃` itself supplies existence.
-/
theorem triangle_morphism_extension
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] (T T' : Triangle C)
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C)
    (g : T.obj₂ ⟶ T'.obj₂) :
    ((T.mor₁ ≫ g ≫ T'.mor₂ = 0 ↔
      ∃ f : T.obj₁ ⟶ T'.obj₁, f ≫ T'.mor₁ = T.mor₁ ≫ g) ∧
    (T.mor₁ ≫ g ≫ T'.mor₂ = 0 ↔
      ∃ h : T.obj₃ ⟶ T'.obj₃, T.mor₂ ≫ h = g ≫ T'.mor₂) ∧
    (T.mor₁ ≫ g ≫ T'.mor₂ = 0 ↔
      ∃ τ : T ⟶ T', τ.hom₂ = g)) ∧
    (Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ T'.obj₃) →
      (∀ (f₁ f₂ : T.obj₁ ⟶ T'.obj₁),
        f₁ ≫ T'.mor₁ = T.mor₁ ≫ g →
        f₂ ≫ T'.mor₁ = T.mor₁ ≫ g → f₁ = f₂) ∧
      (∀ (h₁ h₂ : T.obj₃ ⟶ T'.obj₃),
        T.mor₂ ≫ h₁ = g ≫ T'.mor₂ →
        T.mor₂ ≫ h₂ = g ≫ T'.mor₂ → h₁ = h₂) ∧
      (∀ (f : T.obj₁ ⟶ T'.obj₁) (h : T.obj₃ ⟶ T'.obj₃),
        f ≫ T'.mor₁ = T.mor₁ ≫ g →
        T.mor₂ ≫ h = g ≫ T'.mor₂ →
        ∃ τ : T ⟶ T', τ.hom₁ = f ∧ τ.hom₂ = g ∧ τ.hom₃ = h ∧
          T.mor₃ ≫ f⟦(1 : ℤ)⟧' = h ≫ T'.mor₃)) ∧
    (Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ T.obj₃) →
      ∀ (x : T.obj₃ ⟶ T.obj₁⟦(1 : ℤ)⟧),
        Triangle.mk T.mor₁ T.mor₂ x ∈ distTriang C → x = T.mor₃) := by
  sorry

end CategoryTheory.Pretriangulated
