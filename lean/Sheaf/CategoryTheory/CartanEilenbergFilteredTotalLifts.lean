/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Sheaf.CategoryTheory.CartanEilenbergPresentation
public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
import all Sheaf.CategoryTheory.BoundedBelowSecondFiltration

/-! # Filtered lifts of Cartan--Eilenberg total maps

Source: Stacks Project, Tags 012Z and 015K.
(blueprint: lem-sp-ce-filtered-total-lifts).
-/

@[expose] public section

universe uA vA uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private theorem complex_factor_of_degreewise
    {C : Type uC} [Category.{vC} C] [Abelian C]
    {K K' : CochainComplex C ℤ} (S : Subobject K) (T : Subobject K') (f : K ⟶ K')
    (h : ∀ n : ℤ, (imageSubobject (T.arrow.f n)).Factors (S.arrow.f n ≫ f.f n)) :
    ∃ k : (S : CochainComplex C ℤ) ⟶ (T : CochainComplex C ℤ),
      k ≫ T.arrow = S.arrow ≫ f := by
  have hh (n : ℤ) : ∃ k : (S : CochainComplex C ℤ).X n ⟶
      (T : CochainComplex C ℤ).X n, k ≫ T.arrow.f n = S.arrow.f n ≫ f.f n := by
    have hn := h n
    rw [imageSubobject_mono, Subobject.mk_factors_iff] at hn
    exact hn
  choose k hk using hh
  let g : (S : CochainComplex C ℤ) ⟶ (T : CochainComplex C ℤ) :=
    { f := k
      comm' := by
        intro i j hij
        apply (cancel_mono (T.arrow.f j)).1
        rw [Category.assoc, ← T.arrow.comm, ← Category.assoc, hk, Category.assoc,
          f.comm, ← Category.assoc, S.arrow.comm]
        simp only [Category.assoc, hk] }
  exact ⟨g, by ext n; exact hk n⟩

private theorem secondFiltration_map_factors
    {C : Type uC} [Category.{vC} C] [Abelian C]
    {K K' : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
    [K.HasTotal (ComplexShape.up ℤ)] [K'.HasTotal (ComplexShape.up ℤ)]
    (α : K ⟶ K') (p n : ℤ) :
    ((K'.secondFiltration n).step p).Factors
      (((K.secondFiltration n).step p).arrow ≫
        (HomologicalComplex₂.total.map α (ComplexShape.up ℤ)).f n) := by
  classical
  dsimp only [HomologicalComplex₂.secondFiltration, DecreasingFiltration.step]
  apply HomologicalComplex₂.bounded_factors_finset_sup (Finset.Icc p n)
  intro i hi
  rw [HomologicalComplex₂.ιTotalOrZero_map]
  apply Subobject.factors_of_factors_right
  apply HomologicalComplex₂.bounded_factors_image
  exact Finset.le_sup (f := fun i : ℤ ↦
    imageSubobject (K'.ιTotalOrZero (ComplexShape.up ℤ) (n - i) i n)) hi

/-- Second filtrations exist on all mapped CE totals, and every comparison has a
filtered lift with the specified underlying total map.
Source: Stacks Project, Tags 012Z and 015K
(blueprint: lem-sp-ce-filtered-total-lifts).

Proof. Extension by zero in resolution degree and the negative horizontal vanishing
make the mapped double complex first quadrant. Apply the bounded-below second
filtration construction. Each second step is the finite supremum of the images of
the corresponding total summand inclusions. A mapped comparison takes each such
inclusion to the corresponding target inclusion composed with its component map,
so it preserves the step. Restrict degreewise through the monic step inclusions;
the chain-map equations follow after cancelling those monomorphisms. These restrictions
assemble into a map of subcomplexes, and hence the required filtered map. -/
theorem cartanEilenberg_filtered_total_lifts
    {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    (F : A ⥤ B) [F.Additive] (G : B ⥤ C) [G.Additive] :
    ∃ L : ∀ P : CartanEilenbergPresentation F, DecreasingFiltration (P.total G),
      (∀ (P : CartanEilenbergPresentation F) (p n : ℤ),
        (L P).complexStep p n =
          ((((CartanEilenbergPresentation.mappedFunctor G).obj P.I).secondFiltration n).step p)) ∧
      (∀ (P Q : CartanEilenbergPresentation F) (d : P.Comparison Q),
        ∃ t : (⟨P.total G, L P⟩ : FilteredObject (CochainComplex C ℤ)) ⟶
            (⟨Q.total G, L Q⟩ : FilteredObject (CochainComplex C ℤ)),
          t.hom = HomologicalComplex₂.total.map
            ((CartanEilenbergPresentation.mappedFunctor G).map d.α) (ComplexShape.up ℤ)) := by
  classical
  have hzero (P : CartanEilenbergPresentation F) (i j : ℤ)
      (hij : i < 0 ∨ j < 0) :
      IsZero (((((CartanEilenbergPresentation.mappedFunctor G).obj P.I).X i).X j)) := by
    rcases hij with hi | hj
    · exact (HomologicalComplex.eval C (ComplexShape.up ℤ) j).map_isZero
        ((ComplexShape.embeddingUpNat.extendFunctor C).map_isZero
          ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map_isZero (P.zero_neg i hi)))
    · exact HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat j
        (fun m hm ↦ by change (m : ℤ) = j at hm; omega)
  choose L hL _ _ using fun P : CartanEilenbergPresentation F ↦
    ((CartanEilenbergPresentation.mappedFunctor G).obj P.I).boundedBelow_secondFiltration
      0 (hzero P)
  refine ⟨L, hL, ?_⟩
  intro P Q d
  let f := HomologicalComplex₂.total.map
    ((CartanEilenbergPresentation.mappedFunctor G).map d.α) (ComplexShape.up ℤ)
  refine ⟨⟨f, ?_⟩, rfl⟩
  intro p
  apply complex_factor_of_degreewise
  intro n
  have hh := secondFiltration_map_factors
    ((CartanEilenbergPresentation.mappedFunctor G).map d.α) p n
  rw [← hL P p n, ← hL Q p n] at hh
  have hh' := Subobject.factors_of_factors_right
    (factorThruImageSubobject (((L P).step p).arrow.f n)) hh
  dsimp only [DecreasingFiltration.complexStep] at hh'
  simpa only [← Category.assoc, imageSubobject_arrow_comp] using hh' 

end CategoryTheory
