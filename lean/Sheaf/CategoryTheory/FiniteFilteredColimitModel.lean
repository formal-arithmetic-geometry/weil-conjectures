/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Colimits
public import Sheaf.CategoryTheory.FiniteFiltrationInduction

/-!
# The filtration and graded pieces of a finite filtered colimit

Source: Stacks Project, Tag 0EZM, finite-term comparison in the proof;
Tag 00DB, directed-colimit exactness; Tag 0127, descending filtration induction.
-/

@[expose] public section

universe u

namespace CategoryTheory

open Limits

/-- A uniformly finite filtered diagram has a filtered colimit whose graded pieces
are the colimits of the graded pieces. The cocone is universal for filtered maps.

Source: Stacks Project, Tag 00DB (directed-colimit exactness), Tag 0121 (filtrations),
and the finite-filtration argument in Tag 0EZM.

Proof: use the unique restrictions of a to form the diagrams of filtration steps.
Exactness of directed colimits makes the map from each colimit of filtration steps
into colimit A monic. Define H.step q as this subobject. The consecutive inclusions
make H decreasing. At q=L the step is the whole object; at q=U+1 it is zero, so H
is finite. The maps from the original filtration steps into these colimits make the
canonical colimit legs into filtered maps c. Take the colimit of the short exact
sequence from step q+1 to step q to its graded quotient. Exactness identifies its
cokernel with H.gradedPiece q. The isomorphisms e, compatible by he, identify Q with
the diagram of graded pieces; the resulting colimit isomorphism θ has precisely
the displayed equations with the graded maps of c. For any filtered compatible
cocone b, its restrictions induce maps from the colimits of filtration steps into
the steps of G. These maps prove that the ordinary colimit descent φ is filtered,
giving f. The equality c i ≫ f = b i follows from equality of underlying maps and
proof irrelevance. For empty I, take every step of H to be zero: colimit A and every
colimit Q are zero, and the same construction and equations hold. If U<L, the
original bounds force every A_i to be zero, giving the same zero filtration.
(blueprint: lem-weil-pbc-finite-filtered-colimit-model) -/
theorem finite_filtered_colimit_model
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (A : I ⥤ AddCommGrpCat.{u})
    (F : ∀ i : I, DecreasingFiltration (A.obj i))
    (a : ∀ {i j : I} (_ : i ⟶ j),
      (⟨A.obj i, F i⟩ : FilteredObject AddCommGrpCat.{u}) ⟶ ⟨A.obj j, F j⟩)
    (ha : ∀ {i j : I} (f : i ⟶ j), (a f).hom = A.map f)
    (L U : ℤ)
    (hF : ∀ (i : I) (q : ℤ),
      (q ≤ L → (F i).step q = ⊤) ∧ (U < q → (F i).step q = ⊥)) :
    ∃ (H : DecreasingFiltration (colimit A))
      (c : ∀ i : I, (⟨A.obj i, F i⟩ : FilteredObject AddCommGrpCat.{u}) ⟶
        ⟨colimit A, H⟩),
      (∀ i : I, (c i).hom = colimit.ι A i) ∧ H.IsFinite ∧
      (∀ (q : ℤ) (Q : I ⥤ AddCommGrpCat.{u})
        (e : ∀ i : I, Q.obj i ≅ (F i).gradedPiece q),
        (∀ {i j : I} (f : i ⟶ j),
          Q.map f ≫ (e j).hom = (e i).hom ≫ FilteredObject.gradedMap (a f) q) →
        ∃ θ : colimit Q ⟶ H.gradedPiece q,
          (∀ i : I, colimit.ι Q i ≫ θ = (e i).hom ≫
            FilteredObject.gradedMap (c i) q) ∧ IsIso θ) ∧
      (∀ (B : AddCommGrpCat.{u}) (G : DecreasingFiltration B)
        (b : ∀ i : I,
          (⟨A.obj i, F i⟩ : FilteredObject AddCommGrpCat.{u}) ⟶ ⟨B, G⟩),
        (∀ {i j : I} (f : i ⟶ j), A.map f ≫ (b j).hom = (b i).hom) →
        ∀ φ : colimit A ⟶ B,
          (∀ i : I, colimit.ι A i ≫ φ = (b i).hom) →
          ∃ f : (⟨colimit A, H⟩ : FilteredObject AddCommGrpCat.{u}) ⟶ ⟨B, G⟩,
            f.hom = φ ∧ ∀ i : I, c i ≫ f = b i) := by
  sorry

end CategoryTheory
