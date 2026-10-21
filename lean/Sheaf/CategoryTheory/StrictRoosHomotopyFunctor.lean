/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Sheaf.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.CategoryTheory.Linear.FunctorCategory

/-!
# The strict Roos functor on compatible homotopies

Source: Stacks Project, derived.tex, Tags 014E (definition-cone),
08TC (definition-derived-limit), 013H (definition-complexes-notation),
and dga.tex, Tag 09MJ (definition-linear-category).
(blueprint: lem-pur-strict-roos-homotopy-functor)
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory.Limits Opposite

namespace CategoryTheory

universe u v w

/-- The fixed strict Roos cone is additive, sends a compatible tower homotopy to the
signed diagonal product homotopy, and descends to an additive functor on homotopy
categories. Both functors are linear whenever the coefficient category is linear.
The two projection equations express exactly `(-h_P y, h_P x)` in the coordinates
`roosχ`, without treating objects of an arbitrary abelian category as sets.

Source: Stacks Project, derived.tex, Tags 014E (definition-cone),
08TC (definition-derived-limit), 013H (definition-complexes-notation);
homology.tex, Tag 0112; dga.tex, Tag 09MJ (definition-linear-category).
(blueprint: lem-pur-strict-roos-homotopy-functor)

Proof plan:
1. Use the universal property of termwise products: product maps preserve identities,
composition and addition, since these equations hold after every projection.
2. Strictness gives `s_Y F = F s_X`, hence `v_Y F = F v_X`. The diagonal product maps
therefore commute with the signed cone differential and give the existing `roosF`.
3. The same projection calculation proves additivity of this cochain functor.
4. A homotopy in the tower category has natural-transformation components: these are
exactly the transition-compatible levelwise homotopies. Products give `F-G=dH+Hd`
and `v_Y H = H v_X`, without any exactness hypothesis on products.
5. For `T(y,x)=(-Hy,Hx)`, compute `DT+TD`. Its diagonal blocks are `dH+Hd`;
the off-diagonal block is `Hv_X-v_Y H=0`. This proves the two signed projection
formulas below and the homotopy equation.
6. Homotopy is a congruence: zero, negation and addition give reflexivity, symmetry
and transitivity, and composition sends a homotopy to `b h a`. All preserve tower
compatibility. Thus chain maps modulo compatible homotopy form the stated source.
7. Descend `roosF` using this congruence. Its quotient factorization gives precisely
`X ↦ R(X)` and `[f] ↦ [R(f)]`; identities, composition and addition descend as well.
8. In a linear category, products and biproduct components commute with scalars.
Multiplying a homotopy by a scalar preserves its equation and transition compatibility.
Thus both the cochain functor and its homotopy quotient preserve scalars.
The definitions used are def-weil-strict-roos-model, def-weil-inverse-system,
def-weil-abstract-derived-category, def-sp-abelian, def-weil-category-product,
and def-weil-linear-category. -/
theorem roosF_homotopy_functor
    {A : Type u} [Category.{v} A] [Abelian A] [HasCountableProducts A] :
    (roosF (A := A)).Additive ∧
    (∀ (X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (f g : X ⟶ Y) (h : Homotopy f g),
      ∃ H : Homotopy (roosF.map f) (roosF.map g), ∀ (p : ℤ) (n : ℕ),
        (H.hom ((p + 1) + 1) (p + 1) ≫ (roosχ Y p).hom ≫ biprod.fst ≫
          (Pi.π (fun m : ℕ ↦ Y.asFunctor.obj (op m)) n).f p =
          -((roosχ X (p + 1)).hom ≫ biprod.fst ≫
            (Pi.π (fun m : ℕ ↦ X.asFunctor.obj (op m)) n).f (p + 1) ≫
            (h.hom (p + 1) p).app (op n))) ∧
        (H.hom ((p + 1) + 1) (p + 1) ≫ (roosχ Y p).hom ≫ biprod.snd ≫
          (Pi.π (fun m : ℕ ↦ Y.asFunctor.obj (op m)) n).f (p + 1) =
          (roosχ X (p + 1)).hom ≫ biprod.snd ≫
            (Pi.π (fun m : ℕ ↦ X.asFunctor.obj (op m)) n).f ((p + 1) + 1) ≫
            (h.hom ((p + 1) + 1) (p + 1)).app (op n))) ∧
    (∃ RF : HomotopyCategory (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ) ⥤
        HomotopyCategory A (ComplexShape.up ℤ),
      RF.Additive ∧
      HomotopyCategory.quotient (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ) ⋙ RF =
        roosF ⋙ HomotopyCategory.quotient A (ComplexShape.up ℤ) ∧
      ∀ (k : Type w) [CommRing k] [Linear k A],
        (roosF (A := A)).Linear k ∧ RF.Linear k) := by
  sorry

end CategoryTheory
