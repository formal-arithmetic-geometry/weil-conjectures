/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Colimits
public import Sheaf.CategoryTheory.FiniteFiltrationInduction
import Sheaf.CategoryTheory.FiniteFilteredColimitModel

/-!
# Comparison of uniformly finite filtered colimits

Source: Stacks Project, Tag 0EZM, finite-term comparison in the proof;
Tag 00DB, directed-colimit exactness; Tag 0127, descending filtration induction.
-/

@[expose] public section

universe u

namespace CategoryTheory

open Limits

private theorem restriction_arrow {X Y : FilteredObject AddCommGrpCat.{u}}
    (f : X ⟶ Y) (q : ℤ) :
    FilteredObject.restriction f q ≫ (Y.filtration.step q).arrow =
      (X.filtration.step q).arrow ≫ f.hom :=
  Classical.choose_spec (f.preserves q)

private theorem gradedMap_projection {X Y : FilteredObject AddCommGrpCat.{u}}
    (f : X ⟶ Y) (q : ℤ) :
    cokernel.π (Subobject.ofLE (X.filtration.step (q + 1)) (X.filtration.step q)
      (X.filtration.antitone_step (by omega))) ≫ FilteredObject.gradedMap f q =
    FilteredObject.restriction f q ≫
      cokernel.π (Subobject.ofLE (Y.filtration.step (q + 1)) (Y.filtration.step q)
        (Y.filtration.antitone_step (by omega))) :=
  Classical.choose_spec (FilteredObject.exists_gradedMap X Y f q)

private theorem restriction_comp {X Y Z : FilteredObject AddCommGrpCat.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (q : ℤ) :
    FilteredObject.restriction (f ≫ g) q =
      FilteredObject.restriction f q ≫ FilteredObject.restriction g q := by
  apply (cancel_mono (Z.filtration.step q).arrow).1
  rw [restriction_arrow, Category.assoc, restriction_arrow,
    ← Category.assoc, restriction_arrow]
  rfl

private theorem gradedMap_comp {X Y Z : FilteredObject AddCommGrpCat.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (q : ℤ) :
    FilteredObject.gradedMap (f ≫ g) q =
      FilteredObject.gradedMap f q ≫ FilteredObject.gradedMap g q := by
  apply (cancel_epi (cokernel.π (Subobject.ofLE
    (X.filtration.step (q + 1)) (X.filtration.step q)
    (X.filtration.antitone_step (by omega))))).1
  rw [gradedMap_projection, ← Category.assoc, gradedMap_projection,
    Category.assoc, gradedMap_projection, restriction_comp, Category.assoc]

/-- Uniformly finite filtrations reduce colimit comparison to graded comparison.

The graded diagrams are supplied up to compatible isomorphisms, so this statement
can be used with spectral-sequence pages as models for the graded pieces.

Source: Stacks Project, Tag 0EZM, finite-term comparison in the proof;
Tag 00DB and the descending induction in Tag 0127.

Proof: apply finite_filtered_colimit_model to obtain a finite filtration H on
colimit A, its filtered cocone c, compatible graded colimit isomorphisms θ, and
filtered descent f of the supplied φ. The target filtration is finite with bounds
L and U+1. For each q, choose the graded model Q and its target isomorphism ψ from
hgraded. The cocone equations and functoriality of gradedMap give
θ followed by gradedMap f q = ψ, checked by colimit.hom_ext. Hence gradedMap f q
is inv θ followed by ψ and is an isomorphism. Apply the existing
FilteredObject.finite_filtration_induction to f and these graded isomorphisms.
Its underlying map equals φ, which proves the conclusion. Functoriality of gradedMap
is proved here by cancelling the source cokernel projection and using uniqueness
of the restrictions through the target monic inclusion.
(blueprint: lem-weil-pbc-finite-filtered-colimit-comparison) -/
theorem finite_filtered_colimit_comparison
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (A : I ⥤ AddCommGrpCat.{u})
    (F : ∀ i : I, DecreasingFiltration (A.obj i))
    (B : AddCommGrpCat.{u}) (G : DecreasingFiltration B)
    (a : ∀ {i j : I} (_ : i ⟶ j),
      (⟨A.obj i, F i⟩ : FilteredObject AddCommGrpCat.{u}) ⟶ ⟨A.obj j, F j⟩)
    (ha : ∀ {i j : I} (f : i ⟶ j), (a f).hom = A.map f)
    (b : ∀ i : I,
      (⟨A.obj i, F i⟩ : FilteredObject AddCommGrpCat.{u}) ⟶ ⟨B, G⟩)
    (hb : ∀ {i j : I} (f : i ⟶ j), A.map f ≫ (b j).hom = (b i).hom)
    (L U : ℤ)
    (hF : ∀ (i : I) (q : ℤ),
      (q ≤ L → (F i).step q = ⊤) ∧ (U < q → (F i).step q = ⊥))
    (hG : ∀ q : ℤ, (q ≤ L → G.step q = ⊤) ∧ (U < q → G.step q = ⊥))
    (hgraded : ∀ q : ℤ, ∃ (Q : I ⥤ AddCommGrpCat.{u})
      (e : ∀ i : I, Q.obj i ≅ (F i).gradedPiece q),
      (∀ {i j : I} (f : i ⟶ j),
        Q.map f ≫ (e j).hom = (e i).hom ≫ FilteredObject.gradedMap (a f) q) ∧
      ∃ ψ : colimit Q ⟶ G.gradedPiece q,
        (∀ i : I, colimit.ι Q i ≫ ψ = (e i).hom ≫
          FilteredObject.gradedMap (b i) q) ∧ IsIso ψ) :
    ∀ φ : colimit A ⟶ B,
      (∀ i : I, colimit.ι A i ≫ φ = (b i).hom) → IsIso φ := by
  obtain ⟨H, c, _hc, hH, hcompare, hdesc⟩ :=
    finite_filtered_colimit_model A F a ha L U hF
  intro φ hφ
  obtain ⟨f, hf, hcf⟩ := hdesc B G b hb φ hφ
  have hGfinite : G.IsFinite :=
    ⟨L, U + 1, (hG L).1 le_rfl, (hG (U + 1)).2 (by omega)⟩
  have hgr : ∀ q : ℤ, IsIso (FilteredObject.gradedMap f q) := by
    intro q
    obtain ⟨Q, e, he, ψ, hψ, hψiso⟩ := hgraded q
    obtain ⟨θ, hθ, hθiso⟩ := hcompare q Q e he
    have hcomp : θ ≫ FilteredObject.gradedMap f q = ψ := by
      apply colimit.hom_ext
      intro i
      rw [← Category.assoc, hθ, Category.assoc, ← gradedMap_comp, hcf]
      exact (hψ i).symm
    have : IsIso θ := hθiso
    have : IsIso ψ := hψiso
    have heq : FilteredObject.gradedMap f q = inv θ ≫ ψ := by
      rw [← hcomp]
      simp
    rw [heq]
    infer_instance
  have hiso := (FilteredObject.finite_filtration_induction
    ⟨colimit A, H⟩ ⟨B, G⟩ f hH hGfinite hgr).1
  rw [hf] at hiso
  exact hiso

end CategoryTheory
