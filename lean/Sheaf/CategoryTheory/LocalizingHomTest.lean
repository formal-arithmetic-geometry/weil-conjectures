/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosure
import Mathlib.CategoryTheory.Triangulated.Orthogonal

/-! # Shifted generators detect isomorphisms on their localizing closure

Source: the blueprint, `sec-six-functors-basics/sk-prop-sf-rf-shriek-preservation`,
closed-adjoint uniqueness and final restriction paragraphs; Stacks Project, Derived Categories,
Tags 0145, 0146, 0149, 0FXC and 05QR (blueprint: lem-sf-localizing-hom-test).

The class of generators is an arbitrary object property. The localizing closure is the existing
intersection of replete triangulated subcategories closed under coproducts indexed in the Hom
universe; neither smallness nor compactness of the generator class is required.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ObjectProperty

/-- A morphism between objects of the localizing closure of an arbitrary class is invertible
if postcomposition induces bijections on Hom from every integer shift of every generator.

Source: the blueprint, `sk-prop-sf-rf-shriek-preservation`, closed-adjoint uniqueness and final
restriction paragraphs; Stacks Project, Derived Categories, Tags 0145, 0146, 0149, 0FXC and 05QR
(blueprint: lem-sf-localizing-hom-test).

Proof plan:
1. Complete `α : B ⟶ G` to a distinguished triangle `B ⟶ G ⟶ K ⟶ B[1]`. Every replete
   triangulated coproduct-closed subcategory containing the generators contains `B` and `G`,
   hence `K` by rotation and extension closure. Thus `K` belongs to the localizing closure
   (`def-weil-triangulated-category`, `def-weil-triangulated-subcategory`).
2. For a shifted generator `W = X[n]`, injectivity of postcomposition by `α[1]` follows from
   the hypothesis for `X[n-1]`. If `f : W ⟶ K`, consecutive composites in the triangle give
   `f ≫ δ ≫ α[1] = 0`, so injectivity gives `f ≫ δ = 0`. Hom-exactness gives `f = g ≫ p`;
   surjectivity writes `g = h ≫ α`, and `α ≫ p = 0` gives `f = 0`
   (`lem-weil-pbc-hom-into-triangle-exact`, Stacks 0146 and 0149).
3. Let `Q` be the replete class of all integer shifts of `K`. It is shift-stable, so its
   left orthogonal is replete and triangulated (`lem-sf-shift-stable-left-orthogonal`,
   Stacks 0FXC). It is closed under small coproducts: every map from a coproduct into an
   object of `Q` restricts to zero on each summand, hence is zero by coproduct uniqueness.
   This includes the empty coproduct.
4. Inverse shifts identify maps from a generator to `K[m]` with maps from its `[-m]` shift
   to `K`, so step 2 puts every generator in this left orthogonal. Consequently it contains
   the localizing closure, hence `K`. Since `K` itself is in `Q` up to the shift-zero
   isomorphism, its identity is zero and `K` is a zero object. No coproduct indexed by
   the generator class is used.
5. The zero-cone criterion gives `IsIso α` (`lem-kun-distinguished-cone-zero`, Stacks 05QR).
-/
theorem isIso_of_bijective_postcomp_shift_generators
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    [HasCoproducts.{v} C] (S : ObjectProperty C) {B G : C} (α : B ⟶ G)
    (hB : S.localizingClosure B) (hG : S.localizingClosure G)
    (hα : ∀ (X : C), S X → ∀ (n : ℤ),
      Function.Bijective (fun (f : X⟦n⟧ ⟶ B) ↦ f ≫ α)) : IsIso α := by
  sorry

end CategoryTheory.ObjectProperty
