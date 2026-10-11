/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.Topology.SheafFiniteRelationTruncations
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Finite truncations of a sheaf coequalizer presentation

Source: Stacks Project, Modules, proof of Lemma 17.19.2 (Tag 0CAI), final sentence
(blueprint: lem-weil-pbc-sheaf-finite-truncation-colimit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace TopCat

/-- A sheaf coequalizer presentation with finite supports is the directed colimit of its
finite truncations. `C` and `D` are the supplied coproduct cofans, `κ` and `δ` their canonical
inclusions. `L` is exactly the set of finite pairs admitting both relation factorizations.
The order is componentwise subset inclusion, written explicitly. The last clause is the
colimit universal property in the category of sheaves, without choosing a functor encoding.
Source: Stacks Project, Modules, proof of Lemma 17.19.2 (Tag 0CAI), final sentence
(blueprint: lem-weil-pbc-sheaf-finite-truncation-colimit).

Proof:
1. Subcoproduct inclusions are monomorphisms, by
   lem-weil-pbc-sheaf-coproduct-finite-subcoproducts, so the factorizations are unique.
   The empty pair belongs to L. Unions of two pairs belong to L: assemble their relation
   maps on summands, whose values on overlaps agree after the monic inclusion into C.
   Coproduct universal properties (def-weil-pbc-category-colimit) give composition of
   inclusions and compatibility of truncated relations.
2. Choose the truncated coequalizers (lem-weil-pbc-sheaves-colimit-sheafification).
   Their universal properties give unique transition and cocone maps, because the proposed
   maps coequalize the relations. Coequalizer maps are epis, so checking after their maps
   proves the identity, composition and cocone laws (def-weil-pbc-category-colimit).
3. Every a occurs in the pair (empty, {a}). Every b occurs in a pair ({b}, A_b) by the
   finite-support hypothesis, supplied in applications by
   lem-weil-pbc-sheaf-finite-relation-truncations.
4. For any compatible cocone j into M, use the singleton a stages to assemble C → M.
   Its restriction to each finite C agrees with j composed with the finite coequalizer.
   Each b occurs at a finite stage, so this map equalizes r and s. Descend through the
   supplied coequalizer to obtain F → M; the epi finite coequalizers verify its triangles
   (def-weil-pbc-category-colimit).
5. Any second map with the same triangles agrees after each singleton a coprojection,
   hence after C → F, and therefore agrees since this coequalizer map is epi.
   This is the colimit universal property (def-weil-pbc-category-colimit). -/
theorem sheaf_finite_truncation_colimit
    (X : TopCat.{u}) (A B : Type u) (U : A → Opens X) (V : B → Opens X)
    (S : A → Type u) (T : B → Type u)
    (C : ∀ P : Set A, Cofan (fun a : P ↦ extensionByEmptyConstant (U a.val) (S a.val)))
    (D : ∀ P : Set B, Cofan (fun b : P ↦ extensionByEmptyConstant (V b.val) (T b.val)))
    (hC : ∀ P, IsColimit (C P)) (hD : ∀ P, IsColimit (D P))
    (κ : ∀ (P Q : Set A), P ⊆ Q → ((C P).pt ⟶ (C Q).pt))
    (δ : ∀ (P Q : Set B), P ⊆ Q → ((D P).pt ⟶ (D Q).pt))
    (hκ : ∀ (P Q : Set A) (h : P ⊆ Q) (a : P),
      (C P).inj a ≫ κ P Q h = (C Q).inj ⟨a.val, h a.property⟩)
    (hδ : ∀ (P Q : Set B) (h : P ⊆ Q) (b : P),
      (D P).inj b ≫ δ P Q h = (D Q).inj ⟨b.val, h b.property⟩)
    (r s : (D Set.univ).pt ⟶ (C Set.univ).pt)
    (F : Cofork r s) (hF : IsColimit F)
    (hfinite : ∀ P : Set B, P.Finite → ∃ Q : Set A, Q.Finite ∧
      ∃ r' s' : (D P).pt ⟶ (C Q).pt,
        r' ≫ κ Q Set.univ (Set.subset_univ Q) = δ P Set.univ (Set.subset_univ P) ≫ r ∧
        s' ≫ κ Q Set.univ (Set.subset_univ Q) = δ P Set.univ (Set.subset_univ P) ≫ s)
    (L : Set (Set B × Set A))
    (hL : ∀ p : Set B × Set A, p ∈ L ↔ p.1.Finite ∧ p.2.Finite ∧
      ∃ r' s' : (D p.1).pt ⟶ (C p.2).pt,
        r' ≫ κ p.2 Set.univ (Set.subset_univ p.2) =
          δ p.1 Set.univ (Set.subset_univ p.1) ≫ r ∧
        s' ≫ κ p.2 Set.univ (Set.subset_univ p.2) =
          δ p.1 Set.univ (Set.subset_univ p.1) ≫ s) :
    (∀ i : L, ∃! z : ((D i.val.1).pt ⟶ (C i.val.2).pt) ×
        ((D i.val.1).pt ⟶ (C i.val.2).pt),
      z.1 ≫ κ i.val.2 Set.univ (Set.subset_univ i.val.2) =
        δ i.val.1 Set.univ (Set.subset_univ i.val.1) ≫ r ∧
      z.2 ≫ κ i.val.2 Set.univ (Set.subset_univ i.val.2) =
        δ i.val.1 Set.univ (Set.subset_univ i.val.1) ≫ s) ∧
    Nonempty L ∧
    (∀ i j : L, ∃ k : L,
      i.val.1 ⊆ k.val.1 ∧ i.val.2 ⊆ k.val.2 ∧
      j.val.1 ⊆ k.val.1 ∧ j.val.2 ⊆ k.val.2) ∧
    (∀ (R S' : ∀ i : L, (D i.val.1).pt ⟶ (C i.val.2).pt),
      (∀ i : L, R i ≫ κ i.val.2 Set.univ (Set.subset_univ i.val.2) =
        δ i.val.1 Set.univ (Set.subset_univ i.val.1) ≫ r) →
      (∀ i : L, S' i ≫ κ i.val.2 Set.univ (Set.subset_univ i.val.2) =
        δ i.val.1 Set.univ (Set.subset_univ i.val.1) ≫ s) →
      ∀ Q : ∀ i : L, Cofork (R i) (S' i),
      (∀ i : L, IsColimit (Q i)) →
      ∃ (φ : ∀ (i j : L), i.val.1 ⊆ j.val.1 → i.val.2 ⊆ j.val.2 →
          ((Q i).pt ⟶ (Q j).pt)) (c : ∀ i : L, (Q i).pt ⟶ F.pt),
        (∀ (i j : L) (hB : i.val.1 ⊆ j.val.1) (hA : i.val.2 ⊆ j.val.2),
          (Q i).π ≫ φ i j hB hA = κ i.val.2 j.val.2 hA ≫ (Q j).π ∧
          ∀ f : (Q i).pt ⟶ (Q j).pt,
            (Q i).π ≫ f = κ i.val.2 j.val.2 hA ≫ (Q j).π → f = φ i j hB hA) ∧
        (∀ i : L,
          (Q i).π ≫ c i = κ i.val.2 Set.univ (Set.subset_univ i.val.2) ≫ F.π ∧
          ∀ f : (Q i).pt ⟶ F.pt,
            (Q i).π ≫ f = κ i.val.2 Set.univ (Set.subset_univ i.val.2) ≫ F.π → f = c i) ∧
        (∀ i : L, φ i i (Set.Subset.refl _) (Set.Subset.refl _) = 𝟙 (Q i).pt) ∧
        (∀ (i j k : L) (hB : i.val.1 ⊆ j.val.1) (hA : i.val.2 ⊆ j.val.2)
            (kB : j.val.1 ⊆ k.val.1) (kA : j.val.2 ⊆ k.val.2),
          φ i j hB hA ≫ φ j k kB kA = φ i k (hB.trans kB) (hA.trans kA)) ∧
        (∀ (i j : L) (hB : i.val.1 ⊆ j.val.1) (hA : i.val.2 ⊆ j.val.2),
          φ i j hB hA ≫ c j = c i) ∧
        (∀ (M : X.Sheaf (Type u)) (m : ∀ i : L, (Q i).pt ⟶ M),
          (∀ (i j : L) (hB : i.val.1 ⊆ j.val.1) (hA : i.val.2 ⊆ j.val.2),
            φ i j hB hA ≫ m j = m i) →
          ∃! f : F.pt ⟶ M, ∀ i : L, c i ≫ f = m i)) := by
  sorry

end TopCat
