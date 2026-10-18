/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import WeilConjectures.FromJoel.Algebra.Homology.CochainComplexMinus

/-!
# Functorial bounded-above resolutions by an object class

Source: the Weil conjectures blueprint, `sec-proetale-coefficients`,
`sk-def-sfb-derived-tensor-hom/lem-sfb-derived-monoidal.proof.md`, first three sentences
(blueprint: lem-sfb-functorial-bounded-above-class-resolution).
The objectwise resolution is Stacks Project, Tag 05T7. The functorial strengthening is
`WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.CochainComplexMinus`,
`minusResolutionFunctor` and `minusResolutionNatTrans`; the zero-preserving reduction is
Mathlib's `Algebra.Homology.LeftResolution.Reduced`.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Functorial resolutions on the entire bounded-above category, without an upper bound
as part of an object's data or an additivity assumption on the cover functor `P`.
Containing zero and closure under binary biproducts express closure under all finite
biproducts. The direct-summand condition is stated as in the node, for `U ⊞ V`.

Source: the Weil conjectures blueprint, `sec-proetale-coefficients`,
`sk-def-sfb-derived-tensor-hom/lem-sfb-derived-monoidal.proof.md`, first three sentences;
Stacks Project, Tag 05T7 (objectwise counterpart), and the FromJoel
`LeftResolution.CochainComplexMinus` functorial construction
(blueprint: lem-sfb-functorial-bounded-above-class-resolution).

Proof plan:
1. Apply `lem-sfb-left-resolution-reduced-class`. Take the full subcategory `C` on `F`;
   summand closure makes it idempotent complete. The reduction of the cover datum
   splits off the zero part of `P` (Mathlib `LeftResolution.Reduced`) and supplies a
   preadditive category with zero and finite coproducts, a fully faithful additive
   inclusion `ι : C ⥤ A` whose values all lie in `F`, a zero-preserving functor
   `Q : A ⥤ C`, and an epimorphic natural augmentation `Q ⋙ ι ⟶ 𝟭 A`.
   This uses `def-sp-abelian` and needs neither additivity nor preservation of zero
   morphisms of the original `P`.
2. Apply `lem-sfb-left-resolution-bounded-minus` to that datum. Its finite totalization
   construction gives one functor on the full bounded-above category and a natural
   quasi-isomorphic augmentation; hence it handles maps between different upper bounds.
   The totalization preserves every upper bound of the input. Every resulting term
   is isomorphic to `ι.obj X` for some `X : C`, so it lies in `F` by step 1 and
   iso-closure. This proves all three clauses. -/
theorem exists_functorial_boundedAbove_class_resolution
    {A : Type u} [Category.{v} A] [Abelian A]
    (F : ObjectProperty A) [F.ContainsZero] [F.IsClosedUnderIsomorphisms]
    (h_biproduct : ∀ (U V : A), F U → F V → F (U ⊞ V))
    (h_summand : ∀ (U V : A), F (U ⊞ V) → F U ∧ F V)
    (P : A ⥤ A) (hP : ∀ (M : A), F (P.obj M))
    (ε : P ⟶ 𝟭 A) (hε : ∀ (M : A), Epi (ε.app M)) :
    ∃ (S : CochainComplex.Minus A ⥤ CochainComplex A ℤ)
      (a : S ⟶ CochainComplex.Minus.ι A),
      (∀ (L : CochainComplex.Minus A), QuasiIso (a.app L)) ∧
      (∀ (L : CochainComplex.Minus A) (i : ℤ), F ((S.obj L).X i)) ∧
      (∀ (L : CochainComplex.Minus A) (b : ℤ),
        L.obj.IsStrictlyLE b → (S.obj L).IsStrictlyLE b) := by
  sorry

end CochainComplex
