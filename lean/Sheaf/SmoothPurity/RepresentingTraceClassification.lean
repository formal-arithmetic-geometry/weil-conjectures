/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Classification and normalization of representing traces

Representing traces form a torsor under automorphisms of the representing object.
Fixing the actual natural Hom equivalence removes precisely that freedom.
Source: smooth-purity trace construction, finite diagonal orientation and transported counit.
(blueprint: lem-pur-representing-trace-classification)
-/

@[expose] public section
set_option autoImplicit false

universe u₁ u₂ v₁ v₂
open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  (F : C ⥤ D) {M : C} {U : D}

/-- The counit transpose of a specified comparison isomorphism represents the Hom
functor. Its Hom equivalence is postcomposition with e followed by inverse adjunction.
Source: def-pur-smooth-trace, the displayed counit composite; det-sp-trace-basic (1).
(blueprint: lem-pur-representing-trace-classification) -/
theorem representingTrace_of_iso
    {G : D ⥤ C} (adj : F ⊣ G) (e : M ≅ G.obj U) :
    ∀ K : C, Function.Bijective
      (fun a : K ⟶ M ↦ F.map a ≫ F.map e.hom ≫ adj.counit.app U) := by
  intro K
  let E : (K ⟶ M) ≃ (F.obj K ⟶ U) :=
    e.homToEquiv.trans (adj.homEquiv K U).symm
  have heq : (fun a : K ⟶ M ↦ F.map a ≫ F.map e.hom ≫ adj.counit.app U) = E := by
    funext a
    change _ = (adj.homEquiv K U).symm (a ≫ e.hom)
    rw [adj.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [heq]
  exact E.bijective

/-- A specified orientation determines a unique representing trace with exactly that
adjunct. This is the valid uniqueness statement for the normalized smooth trace.

Proof: take the inverse adjunction image of e.hom. The preceding theorem proves
representability. The two inverse laws of the adjunction give its adjunct and the
uniqueness. The construction uses the supplied comparison, never a choice among
arbitrary representing traces.
Source: def-pur-smooth-trace and sk-thm-purity-transport, Step 3 (counit preservation).
(blueprint: lem-pur-representing-trace-classification) -/
theorem existsUnique_trace_of_orientation
    {G : D ⥤ C} (adj : F ⊣ G) (e : M ≅ G.obj U) :
    ∃! t : F.obj M ⟶ U,
      (∀ K : C, Function.Bijective (fun a : K ⟶ M ↦ F.map a ≫ t)) ∧
      adj.homEquiv M U t = e.hom := by
  refine ⟨(adj.homEquiv M U).symm e.hom, ⟨?_, ?_⟩, ?_⟩
  · rw [adj.homEquiv_counit]
    exact representingTrace_of_iso F adj e
  · exact (adj.homEquiv M U).apply_symm_apply e.hom
  · intro t ht
    exact (adj.homEquiv M U).injective
      (ht.2.trans ((adj.homEquiv M U).apply_symm_apply e.hom).symm)

/-- Precomposition with a source automorphism preserves the representing property.
The induced Hom map is the original bijection after the bijection a ↦ a ≫ e.hom.
Source: the automorphism ambiguity in the unnormalized smooth trace predicate.
(blueprint: lem-pur-representing-trace-classification) -/
theorem representingTrace_precompose_iso
    (t : F.obj M ⟶ U)
    (ht : ∀ K : C, Function.Bijective (fun a : K ⟶ M ↦ F.map a ≫ t))
    (e : M ≅ M) :
    ∀ K : C, Function.Bijective (fun a : K ⟶ M ↦ F.map a ≫ (F.map e.hom ≫ t)) := by
  intro K
  have heq : (fun a : K ⟶ M ↦ F.map a ≫ (F.map e.hom ≫ t)) =
      (fun a : K ⟶ M ↦ F.map a ≫ t) ∘ (fun a : K ⟶ M ↦ a ≫ e.hom) := by
    funext a
    simp only [Function.comp_apply, Functor.map_comp, Category.assoc]
  rw [heq]
  apply (ht K).comp
  constructor
  · intro a b h
    exact (cancel_mono e.hom).1 h
  · intro a
    exact ⟨a ≫ e.inv, by simp⟩

/-- Any two representing traces differ by a unique source automorphism.

Proof: represent t' using t and t using t', obtaining a and b. Injectivity of
both representing maps at M makes a and b inverse. Injectivity for t also gives
uniqueness of the automorphism. Conversely an automorphism preserves all Hom
bijections by the preceding theorem. This includes zero objects and empty Hom sets;
existence of a representing trace is the only assumption.
Source: the Yoneda uniqueness step in the smooth-purity trace construction.
(blueprint: lem-pur-representing-trace-classification) -/
theorem representingTrace_iff_existsUnique_iso
    (t : F.obj M ⟶ U)
    (ht : ∀ K : C, Function.Bijective (fun a : K ⟶ M ↦ F.map a ≫ t))
    (t' : F.obj M ⟶ U) :
    (∀ K : C, Function.Bijective (fun a : K ⟶ M ↦ F.map a ≫ t')) ↔
      ∃! e : M ≅ M, F.map e.hom ≫ t = t' := by
  constructor
  · intro ht'
    obtain ⟨a, ha⟩ := (ht M).surjective t'
    obtain ⟨b, hb⟩ := (ht' M).surjective t
    have hab : a ≫ b = 𝟙 M := by
      apply (ht' M).injective
      simp only [Functor.map_comp, Category.assoc, hb, ha, F.map_id,
        Category.id_comp]
    have hba : b ≫ a = 𝟙 M := by
      apply (ht M).injective
      simp only [Functor.map_comp, Category.assoc, ha, hb, F.map_id,
        Category.id_comp]
    refine ⟨⟨a, b, hab, hba⟩, ha, ?_⟩
    intro e he
    apply Iso.ext
    exact (ht M).injective (he.trans ha.symm)
  · rintro ⟨e, he, _⟩
    rw [← he]
    exact representingTrace_precompose_iso F t ht e

/-- Once a representing trace exists, unnormalized uniqueness is equivalent to the
absence of nontrivial automorphisms of its source. This is the exact extra assertion
that the disputed smooth trace theorem would require, and it fails for the coefficient
unit in characteristic zero.

Proof: uniqueness identifies every automorphism's transformed trace with t; the
representing injection then identifies its hom with identity. In the reverse direction,
classify each other trace by its unique automorphism, which must be identity.
Source: the representing-pair uniqueness step of the smooth trace route.
(blueprint: lem-pur-representing-trace-classification) -/
theorem existsUnique_representingTrace_iff
    (t : F.obj M ⟶ U)
    (ht : ∀ K : C, Function.Bijective (fun a : K ⟶ M ↦ F.map a ≫ t)) :
    (∃! t' : F.obj M ⟶ U,
      ∀ K : C, Function.Bijective (fun a : K ⟶ M ↦ F.map a ≫ t')) ↔
      ∀ e : M ≅ M, e.hom = 𝟙 M := by
  constructor
  · intro h e
    have he := h.unique (representingTrace_precompose_iso F t ht e) ht
    apply (ht M).injective
    simpa only [F.map_id, Category.id_comp] using he
  · intro h
    refine ⟨t, ht, ?_⟩
    intro t' ht'
    obtain ⟨e, he, _⟩ := (representingTrace_iff_existsUnique_iso F t ht t').1 ht'
    simpa only [h e, F.map_id, Category.id_comp] using he.symm

/-- A specified natural Hom equivalence determines one representing trace, including
its actual Hom maps. The trace is E_M(id), not an arbitrary representing witness.

Proof: naturality with b = id proves its normalization. That normalization identifies
its Hom map with E_K, so it is bijective. Evaluation at id proves uniqueness. No
adjunction, smoothness, or geometric existence theorem is assumed here: constructing
the normalized E from finite purity and reconstruction remains a separate geometric step.
Source: current blueprint def-pur-smooth-trace and det-sp-trace-basic, part (1).
(blueprint: lem-pur-representing-trace-classification) -/
theorem existsUnique_trace_of_normalized_pairing
    (E : ∀ K : C, (K ⟶ M) ≃ (F.obj K ⟶ U))
    (hE : ∀ (K L : C) (a : K ⟶ L) (b : L ⟶ M),
      E K (a ≫ b) = F.map a ≫ E L b) :
    ∃! t : F.obj M ⟶ U,
      (∀ K : C, Function.Bijective (fun a : K ⟶ M ↦ F.map a ≫ t)) ∧
      ∀ (K : C) (a : K ⟶ M), F.map a ≫ t = E K a := by
  have hn : ∀ (K : C) (a : K ⟶ M), F.map a ≫ E M (𝟙 M) = E K a := by
    intro K a
    simpa only [Category.comp_id] using (hE K M a (𝟙 M)).symm
  refine ⟨E M (𝟙 M), ⟨?_, hn⟩, ?_⟩
  · intro K
    have heq : (fun a : K ⟶ M ↦ F.map a ≫ E M (𝟙 M)) = E K := funext (hn K)
    rw [heq]
    exact (E K).bijective
  · intro t ht
    simpa only [F.map_id, Category.id_comp] using ht.2 M (𝟙 M)

end AlgebraicGeometry.ProEtale.CondensedRing
