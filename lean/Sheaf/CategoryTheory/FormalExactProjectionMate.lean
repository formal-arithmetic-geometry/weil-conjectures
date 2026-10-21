/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.CategoryTheory.Triangulated.Basic
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# The formal exact projection mate

Source: Stacks Project, Cohomology on Sites, Tag 0B56, equation-projection-formula-map;
Derived Categories, Tags 014V, 014Y, 0A8D
(blueprint: lem-weil-pbc-formal-exact-projection-mate).

The tensor products are bifunctors, with no associator or left unit assumed.
The comparison and mate below are actual morphisms, defined from the specified data.
-/

@[expose] public section

universe u₁ v₁ u₂ v₂

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

/-- The counit followed by tensoring, before taking its adjunct.
Source: Stacks Tag 0B56, equation-projection-formula-map
(blueprint: lem-weil-pbc-formal-exact-projection-mate). -/
def formalProjectionBeta (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
    (L : C ⥤ D) (R : D ⥤ C) (adj : L ⊣ R)
    (μ : ∀ M N : C, L.obj ((TC.obj M).obj N) ≅ (TD.obj (L.obj M)).obj (L.obj N))
    (E : D) (P : C) :
    L.obj ((TC.obj (R.obj E)).obj P) ⟶ (TD.obj E).obj (L.obj P) :=
  (μ (R.obj E) P).hom ≫ (TD.map (adj.counit.app E)).app (L.obj P)

/-- The explicit adjunct `η ≫ R(β)` defining the projection mate.
Source: Stacks Tag 0B56, equation-projection-formula-map
(blueprint: lem-weil-pbc-formal-exact-projection-mate). -/
def formalProjectionAlpha (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
    (L : C ⥤ D) (R : D ⥤ C) (adj : L ⊣ R)
    (μ : ∀ M N : C, L.obj ((TC.obj M).obj N) ≅ (TD.obj (L.obj M)).obj (L.obj N))
    (E : D) (P : C) :
    (TC.obj (R.obj E)).obj P ⟶ R.obj ((TD.obj E).obj (L.obj P)) :=
  adj.unit.app _ ≫ R.map (formalProjectionBeta TC TD L R adj μ E P)

/-- The projection mate from specified exact tensor, shift, adjunction and right-unit data.
Source: Stacks Tag 0B56, equation-projection-formula-map; Derived Categories Tags 014V,
014Y, 0A8D (blueprint: lem-weil-pbc-formal-exact-projection-mate).

Proof:
1. Each `TC.obj (R.obj E)` is exact by hypothesis. Compose exact functors first as
   `L ⋙ TD.obj E`, then with `R`, using lem-weil-pbc-triangulated-functor-composite.
   The composite CommShift instances give precisely the stated composite comparisons.
2. For `e : E ⟶ E'` and `p : P ⟶ P'`, naturality of μ and the counit gives
   `L(R(e) ⊗ p) ≫ β(E',P') = β(E,P) ≫ (e ⊗ L(p))`. Apply R and unit naturality
   to obtain simultaneous naturality of α. This is the adjunct formula of
   lem-weil-pbc-adjunction-of-natural-bijection.
3. For each integer n, the second-input compatibility of μ, and shift naturality of
   the tensor map induced by the specific counit ε_E, imply shift compatibility of β.
   Use lem-weil-pbc-commshift-nattrans-comp-whisker for composition and whiskering.
4. Whisker the unit by `TC.obj (R.obj E)`, then compose with Rβ. Unit shift
   compatibility, naturality of R's shift comparison and step 3 give the displayed
   all-integer shift equality. This argument includes n = 0 and negative integers.
5. Exactness makes both image triangles distinguished. Naturality at their first two
   arrows supplies two squares. Naturality at the actual connecting arrow w, followed
   by step 4 for n = 1, supplies the third square of the triangle morphism, as in
   def-weil-pbc-triangles-with-shift.
6. Put k_E = (1_E ⊗ u) ≫ ρ_E. Bifunctoriality, naturality of ρ at ε_E and hunit
   give β(E,oneC) ≫ k_E = L(ρ_RE) ≫ ε_E.
7. Apply R to step 6, substitute α = η ≫ Rβ and use unit naturality at ρ_RE.
   The right triangle identity of the specified adjunction gives the right-unit
   equality, by lem-weil-pbc-adjunction-of-natural-bijection. No invertibility of α
   is asserted or used. -/
theorem formalExactProjectionMate
    (C : Type u₁) (D : Type u₂) [Category.{v₁} C] [Category.{v₂} D]
    [HasZeroObject C] [HasZeroObject D] [Preadditive C] [Preadditive D]
    [HasShift C ℤ] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D] [IsTriangulated C] [IsTriangulated D]
    (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
    [∀ M : C, (TC.obj M).CommShift ℤ] [∀ N : C, (TC.flip.obj N).CommShift ℤ]
    [∀ M : D, (TD.obj M).CommShift ℤ] [∀ N : D, (TD.flip.obj N).CommShift ℤ]
    [∀ M : C, (TC.obj M).IsTriangulated] [∀ N : C, (TC.flip.obj N).IsTriangulated]
    [∀ M : D, (TD.obj M).IsTriangulated] [∀ N : D, (TD.flip.obj N).IsTriangulated]
    [∀ (M M' : C) (f : M ⟶ M'), NatTrans.CommShift (TC.map f) ℤ]
    [∀ (N N' : C) (f : N ⟶ N'), NatTrans.CommShift (TC.flip.map f) ℤ]
    [∀ (M M' : D) (f : M ⟶ M'), NatTrans.CommShift (TD.map f) ℤ]
    [∀ (N N' : D) (f : N ⟶ N'), NatTrans.CommShift (TD.flip.map f) ℤ]
    (oneC : C) (oneD : D) (ρC : TC.flip.obj oneC ≅ 𝟭 C) (ρD : TD.flip.obj oneD ≅ 𝟭 D)
    (L : C ⥤ D) (R : D ⥤ C) [L.CommShift ℤ] [R.CommShift ℤ]
    [L.IsTriangulated] [R.IsTriangulated] (adj : L ⊣ R)
    [NatTrans.CommShift adj.unit ℤ] [NatTrans.CommShift adj.counit ℤ]
    (μ : ∀ M N : C, L.obj ((TC.obj M).obj N) ≅ (TD.obj (L.obj M)).obj (L.obj N))
    (hμnat : ∀ (M M' N N' : C) (f : M ⟶ M') (g : N ⟶ N'),
      L.map ((TC.map f).app N ≫ (TC.obj M').map g) ≫ (μ M' N').hom =
        (μ M N).hom ≫ (TD.map (L.map f)).app (L.obj N) ≫
          (TD.obj (L.obj M')).map (L.map g))
    (hμshift₁ : ∀ (M N : C) (n : ℤ),
      (μ (M⟦n⟧) N).hom ≫ (TD.map ((L.commShiftIso n).hom.app M)).app (L.obj N) ≫
          ((TD.flip.obj (L.obj N)).commShiftIso n).hom.app (L.obj M) =
        L.map (((TC.flip.obj N).commShiftIso n).hom.app M) ≫
          (L.commShiftIso n).hom.app ((TC.obj M).obj N) ≫
            (shiftFunctor D n).map (μ M N).hom)
    (hμshift₂ : ∀ (M N : C) (n : ℤ),
      (μ M (N⟦n⟧)).hom ≫ (TD.obj (L.obj M)).map ((L.commShiftIso n).hom.app N) ≫
          ((TD.obj (L.obj M)).commShiftIso n).hom.app (L.obj N) =
        L.map (((TC.obj M).commShiftIso n).hom.app N) ≫
          (L.commShiftIso n).hom.app ((TC.obj M).obj N) ≫
            (shiftFunctor D n).map (μ M N).hom)
    (u : L.obj oneC ≅ oneD)
    (hunit : ∀ M : C, (μ M oneC).hom ≫ (TD.obj (L.obj M)).map u.hom ≫
      ρD.hom.app (L.obj M) = L.map (ρC.hom.app M)) :
    (∀ E : D, (TC.obj (R.obj E)).IsTriangulated ∧
      ((L ⋙ TD.obj E) ⋙ R).IsTriangulated) ∧
    (∀ (E E' : D) (P P' : C) (e : E ⟶ E') (p : P ⟶ P'),
      (TC.map (R.map e)).app P ≫ (TC.obj (R.obj E')).map p ≫
          formalProjectionAlpha TC TD L R adj μ E' P' =
        formalProjectionAlpha TC TD L R adj μ E P ≫
          R.map ((TD.map e).app (L.obj P) ≫ (TD.obj E').map (L.map p))) ∧
    (∀ (E : D) (n : ℤ) (P : C),
      formalProjectionAlpha TC TD L R adj μ E (P⟦n⟧) ≫
          (((L ⋙ TD.obj E) ⋙ R).commShiftIso n).hom.app P =
        ((TC.obj (R.obj E)).commShiftIso n).hom.app P ≫
          (shiftFunctor C n).map (formalProjectionAlpha TC TD L R adj μ E P)) ∧
    (∀ (E : D) (T : Triangle C), T ∈ distTriang C →
      (TC.obj (R.obj E)).mapTriangle.obj T ∈ distTriang C ∧
      ((L ⋙ TD.obj E) ⋙ R).mapTriangle.obj T ∈ distTriang C ∧
      ∃ t : (TC.obj (R.obj E)).mapTriangle.obj T ⟶
          ((L ⋙ TD.obj E) ⋙ R).mapTriangle.obj T,
        t.hom₁ = formalProjectionAlpha TC TD L R adj μ E T.obj₁ ∧
        t.hom₂ = formalProjectionAlpha TC TD L R adj μ E T.obj₂ ∧
        t.hom₃ = formalProjectionAlpha TC TD L R adj μ E T.obj₃) ∧
    (∀ E : D, formalProjectionAlpha TC TD L R adj μ E oneC ≫
      R.map ((TD.obj E).map u.hom ≫ ρD.hom.app E) = ρC.hom.app (R.obj E)) := by
  sorry

end CategoryTheory
