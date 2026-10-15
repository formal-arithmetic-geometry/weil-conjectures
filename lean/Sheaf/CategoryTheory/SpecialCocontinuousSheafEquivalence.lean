/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings
public import Sheaf.CategoryTheory.SiteCoveringAxioms

/-!
# Special cocontinuous functors induce equivalences of sheaves

Source: Stacks Project, Sites, Lemma 03A0 (lemma-equivalence)
(blueprint: lem-weil-pbc-special-cocontinuous-sheaf-equivalence).
-/

@[expose] public section

universe u

open CategoryTheory

namespace CategoryTheory

/-- Source: Stacks Project, Sites, Lemma 03A0 (lemma-equivalence)
(blueprint: lem-weil-pbc-special-cocontinuous-sheaf-equivalence).

Precomposition with a special cocontinuous functor is an equivalence on sheaves of sets.
The natural isomorphism identifies the forward functor on both sections and sheaf maps.
By `continuousCocontinuous_toposAdjunctionForCoverings`, this precomposition is the inverse image
of the associated morphism of topoi. Thus this also asserts that morphism is an equivalence.

Proof:
1. Apply lem-weil-pbc-continuous-cocontinuous-topos-adjunction using conditions
   (a),(b) of def-weil-pbc-special-cocontinuous-functor. Write its functors as
   `L` (restriction) and `R` (compatible families), its counit as evaluation at
   `(U, id)`, and its unit as the family of restrictions along all `u(A) ⟶ V`.
2. For a section `s` over `U` and an arrow `ψ : u(A) ⟶ u(U)`, condition (d)
   supplies a source cover of `A` and lifts to `U`. Continuity preserves the
   covering pullbacks; the two overlap lifts have equal images under `u`.
   Condition (c) equalizes them locally. Sheaf separatedness gives equality
   on overlaps, and the sheaf condition glues the pullbacks of `s` to a unique
   section over `A`. On a common refinement the same argument proves independence
   of the cover and lifts (def-weil-pbc-sites-and-cohomology).
3. Pull these covers back along arrows `B ⟶ A`. Choice independence proves
   compatibility of the glued sections. The identity cover recovers `s` at
   `(U, id)`. Conversely compatibility and separatedness determine every
   coordinate from this value. The counit is therefore bijective; this does
   not require `(U, id)` to be a final object of the indexing category.
4. At `u(U)` the unit followed by counit evaluation is the identity, since
   restriction along the identity fixes a section. The evaluation is bijective
   by step 3, so the unit is bijective on every image object.
5. Condition (e) covers every `V` by image objects. Naturality, step 4 and
   separatedness show that the unit is injective at every `V`. Given a target
   section, lift its restrictions uniquely on that cover. On overlaps their
   images agree, and the just-proved injectivity at every object identifies
   the lifts. Glue in the source sheaf; separatedness in the target sheaf
   shows the glued section maps to the given one. The unit is surjective.
   Empty covers give singleton section sets and cause no exception.
6. The bijective unit and counit are natural isomorphisms, with natural inverses
   obtained by rearranging their naturality squares. They exhibit `L` and `R`
   as quasi-inverses. The adjunction identifies `L` with the inverse image of
   the associated morphism of topoi, and hence that morphism is an equivalence. -/
theorem specialCocontinuous_sheafEquivalence
    {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
    (J : Precoverage C) (K : Precoverage D)
    (hJ : J.IsSiteForCoverings) (hK : K.IsSiteForCoverings)
    (f : C ⥤ D) (hf : f.IsSpecialCocontinuousForCoverings J K) :
    ∃ e : Sheaf K.toGrothendieck (Type u) ≌ Sheaf J.toGrothendieck (Type u),
      Nonempty (e.functor ⋙ sheafToPresheaf J.toGrothendieck (Type u) ≅
        sheafToPresheaf K.toGrothendieck (Type u) ⋙
          (Functor.whiskeringLeft _ _ (Type u)).obj f.op) := by
  obtain ⟨_, _, _⟩ := hK
  -- First establish continuity using only the chosen covering pullbacks.
  let : f.IsCocontinuous J.toGrothendieck K.toGrothendieck := hf.1
  let : J.HasPullbacks := ⟨by
    intro X Y R b hR
    obtain ⟨I, U, a, rfl⟩ := R.exists_eq_ofArrows
    obtain ⟨P, p, q, hpb, _⟩ := hJ.2.2 I Y U a hR X b
    constructor
    intro Z a ha
    obtain ⟨i⟩ := ha
    exact (hpb i).flip.hasPullback⟩
  have hsheaf (G : Sheaf K.toGrothendieck (Type u))
      (X : C) (R : Presieve X) (hR : R ∈ J X) :
      Presieve.IsSheafFor (f.op ⋙ G.obj) R := by
    let : R.HasPairwisePullbacks := J.hasPairwisePullbacks_of_mem hR
    let : f.PreservesPairwisePullbacks R :=
      ⟨fun Y Z a b ha _ ↦ hf.2.2.1 X Y Z R hR a b ha⟩
    apply (Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks f G.obj R).2
    exact ((isSheaf_iff_isSheaf_of_type _ _).1 G.property).isSheafFor_of_mem_precoverage
      (hf.2.1 X R hR)
  let : f.IsContinuous J.toGrothendieck K.toGrothendieck := ⟨fun G ↦ by
    rw [J.isSheaf_toGrothendieck_iff]
    intro X Y b R hR
    obtain ⟨I, U, a, rfl⟩ := R.exists_eq_ofArrows
    obtain ⟨P, p, q, hpb, hcov⟩ := hJ.2.2 I X U a hR Y b
    rw [← Sieve.ofArrows, ← Sieve.ofArrows_eq_pullback_of_isPullback a hpb]
    exact (Presieve.isSheafFor_iff_generate _).1 (hsheaf G Y _ hcov)⟩
  -- Translate the local lifting and equality conditions into covering sieves.
  have hcp := CoverPreserving.of_isContinuous f J.toGrothendieck K.toGrothendieck
  have heq {X Y : C} (a b : X ⟶ Y) (h : f.map a = f.map b) :
      Sieve.equalizer a b ∈ J.toGrothendieck X := by
    obtain ⟨R, hR, h⟩ := hf.2.2.2.1 X Y a b h
    apply J.toGrothendieck.superset_covering _ (J.generate_mem_toGrothendieck hR)
    exact (Sieve.generate_le_iff _ _).2 h
  have hlift {X Y : C} (a : f.obj X ⟶ f.obj Y) :
      f.imageSieve a ∈ J.toGrothendieck X := by
    obtain ⟨R, hR, h⟩ := hf.2.2.2.2.1 X Y a
    apply J.toGrothendieck.superset_covering _ (J.generate_mem_toGrothendieck hR)
    exact (Sieve.generate_le_iff _ _).2 h
  let : f.IsCoverDense K.toGrothendieck := ⟨fun V ↦ by
    obtain ⟨I, U, a, ha⟩ := hf.2.2.2.2.2 V
    apply K.toGrothendieck.superset_covering _ (K.generate_mem_toGrothendieck ha)
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    exact fun i ↦ Presieve.in_coverByImage f (a i)⟩
  let : f.IsLocallyFull K.toGrothendieck := ⟨fun a ↦ hcp.cover_preserve (hlift a)⟩
  let : f.IsLocallyFaithful K.toGrothendieck :=
    ⟨fun a b h ↦ hcp.cover_preserve (heq a b h)⟩
  -- Cocontinuity and the local conditions also reflect covering sieves.
  let : f.IsDenseSubsite J.toGrothendieck K.toGrothendieck := {
    functorPushforward_mem_iff := by
      intro X S
      refine ⟨fun hS ↦ ?_, hcp.cover_preserve⟩
      apply J.toGrothendieck.transitive (f.cover_lift J.toGrothendieck K.toGrothendieck hS) S
      rintro Y a ⟨Z, b, c, hb, hbc⟩
      apply J.toGrothendieck.transitive (hlift c) (S.pullback a)
      rintro W r ⟨d, hd⟩
      have he : f.map (r ≫ a) = f.map (d ≫ b) := by
        simp only [Functor.map_comp, hd, Category.assoc, hbc]
      apply J.toGrothendieck.superset_covering _ (heq (r ≫ a) (d ≫ b) he)
      intro T t ht
      have ht : (t ≫ r) ≫ a = (t ≫ d) ≫ b := by
        simpa only [Sieve.equalizer, Category.assoc] using ht
      change S ((t ≫ r) ≫ a)
      rw [ht]
      exact S.downward_closed hb (t ≫ d) }
  refine ⟨(f.sheafPushforwardContinuous (Type u)
    J.toGrothendieck K.toGrothendieck).asEquivalence, ?_⟩
  exact ⟨f.sheafPushforwardContinuousCompSheafToPresheafIso _ _ _⟩

end CategoryTheory
