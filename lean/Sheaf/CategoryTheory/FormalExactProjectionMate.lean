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

-- The fixed statement includes first-input shift data, while its conclusions use only
-- second-input shift compatibility. Keep the original hypothesis and binder name.
set_option linter.unusedVariables false in
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
  have hβ (E E' : D) (P P' : C) (e : E ⟶ E') (p : P ⟶ P') :
      L.map ((TC.map (R.map e)).app P ≫ (TC.obj (R.obj E')).map p) ≫
          formalProjectionBeta TC TD L R adj μ E' P' =
        formalProjectionBeta TC TD L R adj μ E P ≫
          ((TD.map e).app (L.obj P) ≫ (TD.obj E').map (L.map p)) := by
    dsimp [formalProjectionBeta]
    rw [← Category.assoc, hμnat]
    simp only [Category.assoc]
    have hn : (TD.obj (L.obj (R.obj E'))).map (L.map p) ≫
          (TD.map (adj.counit.app E')).app (L.obj P') =
        (TD.map (adj.counit.app E')).app (L.obj P) ≫
          (TD.obj E').map (L.map p) :=
      (TD.map (adj.counit.app E')).naturality (L.map p)
    rw [hn]
    have hc : (TD.map (L.map (R.map e))).app (L.obj P) ≫
          (TD.map (adj.counit.app E')).app (L.obj P) =
        (TD.map (adj.counit.app E)).app (L.obj P) ≫
          (TD.map e).app (L.obj P) := by
      simpa only [Functor.comp_map, Functor.id_map, TD.map_comp, NatTrans.comp_app] using
        congrArg (fun f ↦ (TD.map f).app (L.obj P)) (adj.counit.naturality e)
    simpa only [Category.assoc] using congrArg
      (fun f ↦ (μ (R.obj E) P).hom ≫ f ≫ (TD.obj E').map (L.map p)) hc
  have hα (E E' : D) (P P' : C) (e : E ⟶ E') (p : P ⟶ P') :
      (TC.map (R.map e)).app P ≫ (TC.obj (R.obj E')).map p ≫
          formalProjectionAlpha TC TD L R adj μ E' P' =
        formalProjectionAlpha TC TD L R adj μ E P ≫
          R.map ((TD.map e).app (L.obj P) ≫ (TD.obj E').map (L.map p)) := by
    dsimp [formalProjectionAlpha]
    simp only [← Category.assoc]
    rw [← adj.unit_naturality]
    simp only [Category.assoc, ← R.map_comp]
    rw [hβ]
  let m (M : C) : TC.obj M ⋙ L ⟶ L ⋙ TD.obj (L.obj M) :=
    { app := fun P ↦ (μ M P).hom
      naturality := by
        intro P P' p
        simpa using hμnat M M P P' (𝟙 M) p }
  have (M : C) : NatTrans.CommShift (m M) ℤ := ⟨fun n ↦ by
    ext P
    simpa [m, Functor.commShiftIso_comp_hom_app, Category.assoc] using
      (hμshift₂ M P n).symm⟩
  let β (E : D) : TC.obj (R.obj E) ⋙ L ⟶ L ⋙ TD.obj E :=
    m (R.obj E) ≫ Functor.whiskerLeft L (TD.map (adj.counit.app E))
  have (E : D) : NatTrans.CommShift (β E) ℤ := by
    dsimp [β]
    infer_instance
  let α (E : D) : TC.obj (R.obj E) ⟶ (L ⋙ TD.obj E) ⋙ R :=
    (TC.obj (R.obj E)).rightUnitor.inv ≫
      Functor.whiskerLeft (TC.obj (R.obj E)) adj.unit ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight (β E) R
  have (E : D) : NatTrans.CommShift (α E) ℤ := by
    dsimp [α]
    infer_instance
  have hαapp (E : D) (P : C) :
      (α E).app P = formalProjectionAlpha TC TD L R adj μ E P := by
    simp [α, β, m, formalProjectionAlpha, formalProjectionBeta, Functor.map_comp]
  refine ⟨fun E ↦ ⟨inferInstance, inferInstance⟩, hα, ?_, ?_, ?_⟩
  · intro E n P
    simpa only [hαapp] using (NatTrans.shift_app_comm (α E) n P).symm
  · intro E T hT
    refine ⟨Functor.map_distinguished _ T hT, Functor.map_distinguished _ T hT, ?_⟩
    refine ⟨{ hom₁ := (α E).app T.obj₁
              hom₂ := (α E).app T.obj₂
              hom₃ := (α E).app T.obj₃
              comm₁ := (α E).naturality T.mor₁
              comm₂ := (α E).naturality T.mor₂
              comm₃ := ?_ }, hαapp E _, hαapp E _, hαapp E _⟩
    change ((TC.obj (R.obj E)).map T.mor₃ ≫
        ((TC.obj (R.obj E)).commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫
          (shiftFunctor C (1 : ℤ)).map ((α E).app T.obj₁) =
        (α E).app T.obj₃ ≫ ((L ⋙ TD.obj E) ⋙ R).map T.mor₃ ≫
          (((L ⋙ TD.obj E) ⋙ R).commShiftIso (1 : ℤ)).hom.app T.obj₁
    rw [Category.assoc, NatTrans.shift_app_comm, ← Category.assoc,
      (α E).naturality T.mor₃, Category.assoc]
  · intro E
    have hβunit : formalProjectionBeta TC TD L R adj μ E oneC ≫
        ((TD.obj E).map u.hom ≫ ρD.hom.app E) =
          L.map (ρC.hom.app (R.obj E)) ≫ adj.counit.app E := by
      dsimp [formalProjectionBeta]
      simp only [Category.assoc]
      have hn : (TD.map (adj.counit.app E)).app (L.obj oneC) ≫
            (TD.obj E).map u.hom =
          (TD.obj (L.obj (R.obj E))).map u.hom ≫
            (TD.map (adj.counit.app E)).app oneD :=
        ((TD.map (adj.counit.app E)).naturality u.hom).symm
      rw [reassoc_of% hn]
      rw [show (TD.map (adj.counit.app E)).app oneD ≫ ρD.hom.app E =
          ρD.hom.app (L.obj (R.obj E)) ≫ adj.counit.app E from
        ρD.hom.naturality (adj.counit.app E)]
      simpa only [Category.assoc] using
        congrArg (fun f ↦ f ≫ adj.counit.app E) (hunit (R.obj E))
    rw [formalProjectionAlpha, Category.assoc, ← R.map_comp, hβunit, R.map_comp,
      ← Category.assoc, adj.unit_naturality]
    simp

end CategoryTheory
