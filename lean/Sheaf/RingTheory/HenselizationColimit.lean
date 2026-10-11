/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Sheaf.RingTheory.PairHenselization
import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Henselization of pairs commutes with filtered colimits

Source: Stacks Project, More on Algebra, Tags 0A04 and 0A02
(blueprint: lem-weil-pbc-henselization-colimit).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace RingTheory

/-- Clause (1): the unique lifted maps form a directed system of pairs.
Source: Stacks Project, Tag 0A02, functoriality of the left adjoint, used in Tag 0A04
(blueprint: lem-weil-pbc-henselization-colimit).

Proof: Each target henselization is henselian by lem-weil-pbc-pair-henselization.
Apply lem-weil-pbc-henselization-universal-property to the transition map followed by
its target structure map; extension of ideals gives preservation of the stage ideals.
Identity and composition both commute with the structure maps, so uniqueness gives the
identity and composition laws. This is step 1 of the node's proof. -/
theorem pairHenselization_transition_system
    {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
    (F : Λ ⥤ CommRingCat.{u}) (J : ∀ i : Λ, Ideal (F.obj i))
    (hJ : ∀ {i j : Λ} (f : i ⟶ j), Ideal.map (F.map f).hom (J i) ≤ J j)
    (B : Λ → CommRingCat.{u}) (η : ∀ i : Λ, F.obj i ⟶ B i)
    (hB : ∀ i : Λ, ∃ c : Cocone (ObjectProperty.ι
        (fun C : Under (F.obj i) ↦
          AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
            Function.Bijective (Ideal.quotientMap ((J i).map C.hom.hom) C.hom.hom
              (Ideal.le_comap_map)))),
        Nonempty (IsColimit c) ∧ ∃ e : c.pt.right ≅ B i,
          c.pt.hom ≫ e.hom = η i) :
    ∃ t : ∀ {i j : Λ}, (i ⟶ j) → (B i ⟶ B j),
      (∀ {i j : Λ} (f : i ⟶ j),
        (η i ≫ t f = F.map f ≫ η j) ∧
        (∀ g : B i ⟶ B j, η i ≫ g = F.map f ≫ η j → g = t f) ∧
        Ideal.map (t f).hom ((J i).map (η i).hom) ≤ (J j).map (η j).hom) ∧
      (∀ i : Λ, t (𝟙 i) = 𝟙 (B i)) ∧
      (∀ {i j k : Λ} (f : i ⟶ j) (g : j ⟶ k), t (f ≫ g) = t f ≫ t g) := by
  sorry

/-- Clause (2) and the henselian specialization, for the directed system of clause (1).
Source: Stacks Project, More on Algebra, Tag 0A04 and the adjunction in Tag 0A02
(blueprint: lem-weil-pbc-henselization-colimit).

Proof (steps 2--5 of the node):
2. The union of the images of the stage ideals is an ideal by
   lem-weil-pbc-filtered-colimit-algebras-elementwise. Each stage henselization is
   henselian by lem-weil-pbc-pair-henselization, so
   lem-weil-pbc-filtered-colimit-henselian-pair makes the colimit pair henselian.
   The compatible stage structure maps induce eta-infinity by the ring colimit property.
3. Apply lem-weil-pbc-henselization-universal-property to each map from a stage into
   a henselization of the base colimit. Uniqueness makes these maps a cocone, giving u.
   The colimit pair is henselian, so the same universal property gives the reverse map v.
4. Uniqueness on the base and on each stage proves u and v are inverse. Both maps preserve
   the extended ideals, so u carries the colimit ideal exactly onto the extended base ideal.
5. If the base colimit pair is henselian, apply the universal property directly to its
   coprojections to obtain beta_i. Uniqueness proves compatibility. Their induced map beta
   is inverse to eta-infinity by the same argument, and carries the colimit ideal onto I.
The colimits here are arbitrary colimit cocones, as in def-weil-pbc-category-colimit. -/
theorem pairHenselization_colimit
    {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
    (F G : Λ ⥤ CommRingCat.{u}) (η : F ⟶ G)
    (J : ∀ i : Λ, Ideal (F.obj i))
    (hJ : ∀ {i j : Λ} (f : i ⟶ j), Ideal.map (F.map f).hom (J i) ≤ J j)
    (hG : ∀ i : Λ, ∃ c : Cocone (ObjectProperty.ι
        (fun C : Under (F.obj i) ↦
          AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
            Function.Bijective (Ideal.quotientMap ((J i).map C.hom.hom) C.hom.hom
              (Ideal.le_comap_map)))),
        Nonempty (IsColimit c) ∧ ∃ e : c.pt.right ≅ G.obj i,
          c.pt.hom ≫ e.hom = η.app i)
    (c : Cocone F) (hc : IsColimit c) (I : Ideal c.pt)
    (hI : ∀ x : c.pt, x ∈ I ↔
      ∃ (i : Λ) (a : F.obj i), (c.ι.app i).hom a = x ∧ a ∈ J i)
    (d : Cocone G) (hd : IsColimit d) :
    ∃ Ih : Ideal d.pt,
      (∀ x : d.pt, x ∈ Ih ↔ ∃ (i : Λ) (a : G.obj i),
        (d.ι.app i).hom a = x ∧ a ∈ (J i).map (η.app i).hom) ∧
      ∃ ηInf : c.pt ⟶ d.pt,
        (∀ i : Λ, c.ι.app i ≫ ηInf = η.app i ≫ d.ι.app i) ∧
        (∀ (A : CommRingCat.{u}) (ζ : c.pt ⟶ A),
          (∃ ch : Cocone (ObjectProperty.ι
            (fun C : Under c.pt ↦
              AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
                Function.Bijective (Ideal.quotientMap (I.map C.hom.hom) C.hom.hom
                  (Ideal.le_comap_map)))),
            Nonempty (IsColimit ch) ∧ ∃ e : ch.pt.right ≅ A,
              ch.pt.hom ≫ e.hom = ζ) →
          (∃! u : d.pt ⟶ A, ηInf ≫ u = ζ) ∧
          (∀ u : d.pt ⟶ A, ηInf ≫ u = ζ →
            Function.Bijective u.hom ∧ Ideal.map u.hom Ih = I.map ζ.hom)) ∧
        (HenselianRing c.pt I →
          ∃ β : ∀ i : Λ, G.obj i ⟶ c.pt,
            (∀ i : Λ, η.app i ≫ β i = c.ι.app i ∧
              (∀ b : G.obj i ⟶ c.pt, η.app i ≫ b = c.ι.app i → b = β i) ∧
              Ideal.map (β i).hom ((J i).map (η.app i).hom) ≤ I) ∧
            (∀ {i j : Λ} (f : i ⟶ j), G.map f ≫ β j = β i) ∧
            ∃ b : d.pt ⟶ c.pt,
              (∀ i : Λ, d.ι.app i ≫ b = β i) ∧
              Function.Bijective b.hom ∧ Ideal.map b.hom Ih = I) := by
  sorry

end RingTheory
