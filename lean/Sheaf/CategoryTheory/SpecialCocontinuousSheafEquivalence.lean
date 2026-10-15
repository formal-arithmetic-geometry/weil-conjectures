/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings
public import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.CategoryTheory.ContinuousCocontinuousToposAdjunctionForCoverings

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
  sorry

end CategoryTheory
