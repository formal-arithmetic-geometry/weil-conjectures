/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Gluing local immersion loci

Source: Stacks Project, Tag 0BDL, final proof paragraph (gluing characterized loci).
(blueprint: lem-sc-local-immersion-locus).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A base-change-stable, source-local predicate represented locally by immersions
is represented by an immersion over the entire base.
Source: Stacks Project, Tag 0BDL, final proof paragraph, spelling out the gluing.
(blueprint: lem-sc-local-immersion-locus).

Proof:
1. Choose a neighbourhood U_s and its representing immersion for every s.
   The neighbourhoods cover S. On U_s intersect U_t, the two base-changed
   immersions represent the same predicate. Evaluate their universal properties
   on each other to obtain inverse maps; monomorphy of immersions gives uniqueness.
2. These unique isomorphisms satisfy the triple-overlap cocycle identity. The
   overlaps are open in each representative, being inverse images of open
   subschemes of S. Scheme gluing produces W and a map j:W to S. Its restriction
   over each U_s is the original immersion, so j is an immersion by target locality.
3. If g:T to S satisfies P, base-change stability gives P on the inverse-image
   cover of T. The local representing criteria give factors through W. These
   agree on overlaps by monomorphy of j and therefore glue to a global factor.
4. Conversely, given a factor through W, restrict to the inverse-image cover of
   T. On each member the local representing criterion gives P. Source locality
   then gives P globally. For empty S, glue the empty family; for empty T the
   source-locality hypothesis applied to its vacuous pointwise cover gives P. -/
theorem exists_localImmersionLocus (S : Scheme.{u})
    (P : ∀ {T : Scheme.{u}}, (T ⟶ S) → Prop)
    (hbase : ∀ {T T' : Scheme.{u}} (g : T ⟶ S) (h : T' ⟶ T), P g → P (h ≫ g))
    (hsource : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      (∀ t : T, ∃ V : T.Opens, t ∈ V ∧ P (V.ι ≫ g)) → P g)
    (hlocal : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
      ∃ (W : Scheme.{u}) (j : W ⟶ U.toScheme), IsImmersion j ∧
        ∀ {T : Scheme.{u}} (g : T ⟶ U.toScheme),
          (∃ h : T ⟶ W, h ≫ j = g) ↔ P (g ≫ U.ι)) :
    ∃ (W : Scheme.{u}) (j : W ⟶ S), IsImmersion j ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ S), (∃ h : T ⟶ W, h ≫ j = g) ↔ P g := by sorry

end AlgebraicGeometry.Scheme
