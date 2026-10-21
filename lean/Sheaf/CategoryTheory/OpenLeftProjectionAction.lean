/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q12
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Left-coefficient action from normalized open restriction

Source: Stacks Project, Tags 0GL1 and 0E8I, `lemma-j-shriek-and-tensor`, and the
categorical calculation for (G13) in the blueprint `sk-prop-cohsm.proof.md`
(blueprint: lem-pur-open-left-projection-action).

The comparison is the specified swap, right-coefficient comparison, and mapped swap.
Its coherence follows from its restriction normalization, rather than from arbitrary
choices of isomorphisms with the same endpoints.
-/

@[expose] public section

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

open MonoidalCategory BraidedCategory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D]

/-- The specified left-coefficient comparison, obtained by swapping, applying `γ`,
and mapping the swap back. Source: Stacks Tags 0GL1 and 0E8I, the categorical
left-coefficient reformulation of `lemma-j-shriek-and-tensor`
(blueprint: lem-pur-open-left-projection-action). -/
def openLeftProjectionIso [BraidedCategory C] [BraidedCategory D]
    (Q : C ⥤ D) (J : D ⥤ C)
    (γ : ∀ (M : D) (X : C), J.obj M ⊗ X ≅ J.obj (M ⊗ Q.obj X))
    (X : C) (M : D) : X ⊗ J.obj M ≅ J.obj (Q.obj X ⊗ M) :=
  (β_ X (J.obj M)) ≪≫ γ M X ≪≫ J.mapIso (β_ M (Q.obj X))

/-- Naturality, restriction normalization, and the two left-coefficient action laws
for the specified `openLeftProjectionIso`. Source: the categorical lemma for Stacks
Tags 0GL1 and 0E8I, and (G13) in `sk-prop-cohsm.proof.md`.

Proof plan:
1. By `lem-sp-adjunction-unit-fully-faithful-left`, the unit is invertible. Put
   `r M = inv (adj.unit.app M)`. Its naturality follows from unit naturality.
   Compose naturality of the two braidings and of `γ` to obtain naturality of `v`.
2. Move `r` through the mapped swap. Substitute the normalization of `γ`, use
   preservation of braiding by `Q`, move `r` through the braiding, and cancel
   the two swaps. This gives the stated left-coefficient normalization.
3. Equality of `Q`-images detects equality of maps with source `J A`, by the
   injectivity of the adjunction Hom bijection, whose formula is unit followed
   by `Q.map` (`lem-weil-pbc-adjunction-of-natural-bijection`). It also detects
   equality for a source isomorphic to `J A`, by precomposing with that iso.
   Apply this to sources `1 ⊗ J M` and `(X ⊗ Y) ⊗ J M`, using `v` inverses.
4. For the unit law, apply `Q` and postcompose with `r M`. The normalization
   from step 2, left-unitor naturality, and the inverse strong-monoidal
   unit axiom identify both sides. Cancel `r M` and use step 3.
5. For the associativity law, apply `Q` and postcompose with
   `r (Q X ⊗ (Q Y ⊗ M))`. The normalized left side is the composite of
   `δ Q (X ⊗ Y) (J M)`, `δ Q X Y ⊗ r M`, and the target associator.
6. Normalize the right side twice. Naturality of `δ` moves the inner `v`
   past the outer tensorator. It becomes `Q` of the source associator,
   followed by `δ Q X (Y ⊗ J M)`, then `1 ⊗ δ Q Y (J M)`, then
   `1 ⊗ (1 ⊗ r M)`.
7. The inverse strong-monoidal associativity axiom and associator naturality
   identify the two expressions. Cancel `r` and use step 3 to obtain the
   equality in `C` for the original specified composite.
(blueprint: lem-pur-open-left-projection-action). -/
theorem openLeftProjection_action [SymmetricCategory C] [SymmetricCategory D]
    (Q : C ⥤ D) [Q.Braided] (J : D ⥤ C) [J.Full] [J.Faithful] (adj : J ⊣ Q)
    (γ : ∀ (M : D) (X : C), J.obj M ⊗ X ≅ J.obj (M ⊗ Q.obj X))
    (hγ_natural : ∀ (M N : D) (X Y : C) (m : M ⟶ N) (c : X ⟶ Y),
      (J.map m ⊗ₘ c) ≫ (γ N Y).hom =
        (γ M X).hom ≫ J.map (m ⊗ₘ Q.map c))
    (hγ_normalized : ∀ (M : D) (X : C),
      Q.map (γ M X).hom ≫ inv (adj.unit.app (M ⊗ Q.obj X)) =
        Functor.OplaxMonoidal.δ Q (J.obj M) X ≫
          (inv (adj.unit.app M) ⊗ₘ 𝟙 (Q.obj X))) :
    (∀ (X Y : C) (M N : D) (c : X ⟶ Y) (m : M ⟶ N),
      (openLeftProjectionIso Q J γ X M).hom ≫ J.map (Q.map c ⊗ₘ m) =
        (c ⊗ₘ J.map m) ≫ (openLeftProjectionIso Q J γ Y N).hom) ∧
    (∀ (X : C) (M : D),
      Q.map (openLeftProjectionIso Q J γ X M).hom ≫
          inv (adj.unit.app (Q.obj X ⊗ M)) =
        Functor.OplaxMonoidal.δ Q X (J.obj M) ≫
          (𝟙 (Q.obj X) ⊗ₘ inv (adj.unit.app M))) ∧
    (∀ (M : D),
      (openLeftProjectionIso Q J γ (𝟙_ C) M).hom ≫
          J.map ((Functor.OplaxMonoidal.η Q ⊗ₘ 𝟙 M) ≫ (λ_ M).hom) =
        (λ_ (J.obj M)).hom) ∧
    (∀ (X Y : C) (M : D),
      (openLeftProjectionIso Q J γ (X ⊗ Y) M).hom ≫
          J.map ((Functor.OplaxMonoidal.δ Q X Y ⊗ₘ 𝟙 M) ≫
            (α_ (Q.obj X) (Q.obj Y) M).hom) =
        (α_ X Y (J.obj M)).hom ≫
          (𝟙 X ⊗ₘ (openLeftProjectionIso Q J γ Y M).hom) ≫
          (openLeftProjectionIso Q J γ X (Q.obj Y ⊗ M)).hom) := by
  -- The inverse unit is natural because the fully faithful left adjoint has invertible unit.
  have hr {A B : D} (f : A ⟶ B) :
      Q.map (J.map f) ≫ inv (adj.unit.app B) = inv (adj.unit.app A) ≫ f := by
    simp
  -- Move restriction through the specified two swaps and cancel their composite.
  have hn (X : C) (M : D) :
      Q.map (openLeftProjectionIso Q J γ X M).hom ≫
          inv (adj.unit.app (Q.obj X ⊗ M)) =
        Functor.OplaxMonoidal.δ Q X (J.obj M) ≫
          (𝟙 (Q.obj X) ⊗ₘ inv (adj.unit.app M)) := by
    simp only [openLeftProjectionIso, Iso.trans_hom, Functor.mapIso_hom,
      Functor.map_comp, Category.assoc]
    rw [hr, ← Category.assoc (Q.map (γ M X).hom), hγ_normalized]
    rw [Functor.map_braiding]
    simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc]
    rw [← braiding_naturality_assoc]
    simp
  -- Restriction detects equality when the source belongs to the essential image of J.
  have detect {W Z : C} {A : D} (e : W ≅ J.obj A) (f g : W ⟶ Z)
      (h : Q.map f = Q.map g) : f = g := by
    apply (cancel_epi e.inv).mp
    apply (adj.homEquiv A Z).injective
    simp only [Adjunction.homEquiv_unit, Functor.map_comp, h]
  refine ⟨?_, hn, ?_, ?_⟩
  · intro X Y M N c m
    simp only [openLeftProjectionIso, Iso.trans_hom, Functor.mapIso_hom,
      Category.assoc]
    rw [← J.map_comp, ← braiding_naturality, J.map_comp]
    rw [← Category.assoc (γ M X).hom, ← hγ_natural]
    simp only [Category.assoc]
    rw [← Category.assoc (β_ X (J.obj M)).hom, ← braiding_naturality]
    simp only [Category.assoc]
  · intro M
    apply detect (openLeftProjectionIso Q J γ (𝟙_ C) M)
    apply (cancel_mono (inv (adj.unit.app M))).mp
    simp only [Q.map_comp, Category.assoc]
    rw [hr, ← Category.assoc, hn]
    simp only [Category.assoc, tensorHom_comp_tensorHom_assoc, Category.id_comp]
    simp [Functor.OplaxMonoidal.δ_comp_η_tensorHom_assoc]
  · intro X Y M
    apply detect (openLeftProjectionIso Q J γ (X ⊗ Y) M)
    apply (cancel_mono (inv (adj.unit.app (Q.obj X ⊗ (Q.obj Y ⊗ M))))).mp
    simp only [Q.map_comp, Category.assoc]
    rw [hr, ← Category.assoc, hn, hn]
    simp only [Category.assoc, tensorHom_comp_tensorHom_assoc, Category.id_comp]
    rw [← Functor.OplaxMonoidal.δ_natural_assoc]
    simp only [Q.map_id, tensorHom_comp_tensorHom, Category.comp_id]
    rw [hn]
    simp only [tensorHom_def, id_whiskerRight, Category.id_comp,
      whiskerLeft_comp, Category.assoc]
    simp only [Functor.id_obj, whiskerLeft_id, Category.id_comp]
    rw [associator_naturality_right (Z' := M) (Q.obj X) (Q.obj Y)
      (inv (adj.unit.app M))]
    rw [← Functor.OplaxMonoidal.associativity_assoc]
    simp only [Functor.comp_obj]

end CategoryTheory
