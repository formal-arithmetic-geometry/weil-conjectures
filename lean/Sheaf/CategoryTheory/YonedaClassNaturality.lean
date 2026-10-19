/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.CategoryTheory.YonedaExtensionClass

/-! # Naturality of the concrete extension class

Source: Stacks Project, Tag 06XU, functoriality of the class construction.
(blueprint: lem-coef-yoneda-class-naturality)
-/

@[expose] public section

universe u v w

namespace CategoryTheory.YonedaExtension

open Limits Abelian

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]

private theorem normalized_naturality {V₀ U₀ V₁ U₁ V U V' U' : A} {n : ℕ}
    (α : Ext U₀ V₀ n) (β : Ext U₁ V₁ n)
    (l : V₀ ≅ V) (r : U₀ ≅ U) (l' : V₁ ≅ V') (r' : U₁ ≅ U')
    (p : V₀ ⟶ V₁) (q : U₀ ⟶ U₁)
    (h : α.comp (Ext.mk₀ p) (add_zero _) =
      (Ext.mk₀ q).comp β (zero_add _)) :
    (((Ext.mk₀ r.inv).comp α (zero_add _)).comp (Ext.mk₀ l.hom) (add_zero _)).comp
        (Ext.mk₀ (l.inv ≫ p ≫ l'.hom)) (add_zero _) =
      (Ext.mk₀ (r.inv ≫ q ≫ r'.hom)).comp
        (((Ext.mk₀ r'.inv).comp β (zero_add _)).comp
          (Ext.mk₀ l'.hom) (add_zero _)) (zero_add _) := by
  have hh := congrArg (fun x => (Ext.mk₀ r.inv).comp
    (x.comp (Ext.mk₀ l'.hom) (add_zero _)) (zero_add _)) h
  simpa only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
    Ext.mk₀_comp_mk₀_assoc, Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
    Category.comp_id] using hh

set_option backward.isDefEq.respectTransparency false in
/-- The concrete signed composite is natural for every map of exact sequences.
Source: Stacks Project, Tag 06XU, functoriality of the class construction.
Proof: in degree one apply naturality of the short exact connecting class and
cancel the two endpoint isomorphisms. For the induction step, a map of sequences
induces a map on their first cokernels. This gives a morphism of the canonical
short exact heads and a morphism of the smaller-degree tails. Apply the induction
hypothesis to the tails and extClass_naturality to the heads. Associativity of Ext
composition moves the induced cokernel map from one side of the composition to
the other. The common integer sign commutes with both compositions. Cancel the
endpoint isomorphisms, giving the displayed equation. All cuts use actual
cokernels, so the argument applies in every abelian category with HasExt, without
an enough-injectives assumption.
(blueprint: lem-coef-yoneda-class-naturality) -/
theorem derivedClass_naturality (V U V' U' : A) (n : ℕ)
    (E : YonedaExtension A V U (n + 1)) (F : YonedaExtension A V' U' (n + 1))
    (φ : E.sequence ⟶ F.sequence) :
    (E.derivedClass n).comp (Ext.mk₀ (E.leftMap F φ)) (add_zero _) =
      (Ext.mk₀ (E.rightMap F φ)).comp (F.derivedClass n) (zero_add _) := by
  induction n generalizing V U V' U' with
  | zero =>
    have h := normalized_naturality E.shortExact.extClass F.shortExact.extClass
      E.leftIso E.rightIso F.leftIso F.rightIso (φ.app 0) (φ.app (Fin.last 2))
      (E.shortExact.extClass_naturality F.shortExact
        { τ₁ := φ.app 0
          τ₂ := φ.app 1
          τ₃ := φ.app (Fin.last 2)
          comm₁₂ := (ComposableArrows.naturality' φ 0 1).symm
          comm₂₃ := (ComposableArrows.naturality' φ 1 2).symm })
    simpa only [derivedClass, Ext.neg_comp, Ext.comp_neg, leftMap, rightMap] using
      congrArg Neg.neg h
  | succ n ih =>
    have ht := ih _ _ _ _ E.tail F.tail (E.tailMap F φ)
    have hh := E.head_shortExact.extClass_naturality F.head_shortExact (E.headMap F φ)
    have hl : E.tail.leftMap F.tail (E.tailMap F φ) = (E.headMap F φ).τ₃ := by
      change (𝟙 _) ≫ (E.headMap F φ).τ₃ ≫ (𝟙 _) = (E.headMap F φ).τ₃
      simp
    have hr : E.tail.rightMap F.tail (E.tailMap F φ) = E.rightMap F φ := by
      rfl
    rw [hl, hr] at ht
    dsimp only [headMap] at hh ht
    have hraw :
        ((E.tail.derivedClass n).comp E.head_shortExact.extClass
          (show (n + 1) + 1 = n + 2 from rfl)).comp
        (Ext.mk₀ (φ.app 0)) (add_zero _) =
      (Ext.mk₀ (E.rightMap F φ)).comp
        ((F.tail.derivedClass n).comp F.head_shortExact.extClass
          (show (n + 1) + 1 = n + 2 from rfl))
        (zero_add _) := by
      rw [Ext.comp_assoc_of_third_deg_zero, hh,
        ← Ext.comp_assoc_of_second_deg_zero, ht]
      exact Ext.comp_assoc _ _ _ (zero_add (n + 1))
        (show (n + 1) + 1 = n + 2 from rfl) (by omega)
    have hnorm := normalized_naturality
      ((E.tail.derivedClass n).comp E.head_shortExact.extClass (show (n + 1) + 1 = n + 2 from rfl))
      ((F.tail.derivedClass n).comp F.head_shortExact.extClass (show (n + 1) + 1 = n + 2 from rfl))
      E.leftIso (Iso.refl U) F.leftIso (Iso.refl U') (φ.app 0) (E.rightMap F φ) hraw
    simp only [Iso.refl_inv, Iso.refl_hom, Category.comp_id, Category.id_comp,
      Ext.mk₀_id_comp] at hnorm
    rcases neg_one_pow_eq_or ℤ n with hsign | hsign <;>
      simpa only [derivedClass, hsign, one_smul, neg_one_smul,
        Ext.neg_comp, Ext.comp_neg, neg_inj, leftMap] using
        (show _ from hnorm)

end CategoryTheory.YonedaExtension
