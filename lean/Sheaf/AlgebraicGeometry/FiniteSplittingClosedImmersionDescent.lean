/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance

/-! # Descent of finite splitting through a surjective closed immersion

Source: Stacks Project Tag 04DZ and steps 2--3 of
`lem-weil-pbc-generic-finite-noetherian-scheme-splitting`.
(blueprint: lem-weil-pbc-finite-splitting-closed-immersion-descent)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Finite etale-local splitting into universal homeomorphisms descends through a
surjective closed immersion. This is a statement over a fixed open, with no
Noetherian, density, affine, or generic-splitting assumption.

Source: Stacks Project Tag 04DZ; steps 2--3 of
`lem-weil-pbc-generic-finite-noetherian-scheme-splitting`.
(blueprint: lem-weil-pbc-finite-splitting-closed-immersion-descent)

Proof: Restrict r to U. This is again a surjective closed immersion, and hence a
universal homeomorphism. The equivalence of small etale sites lifts each scheme
of the given cover and its structural map to U. The lifted maps jointly cover U:
their base changes do, and the vertical maps are homeomorphisms on points.
Pulling back the finite source to a lifted cover gives a surjective closed
immersion from the old source. Transport its finite disjoint open partition
along this homeomorphism. Each open in a finite disjoint open partition is also
closed, so its inclusion is finite, and its map to the lifted cover is finite.
For each transported piece, the old piece is its base change along the
surjective closed immersion of covers. The old component map is universally
bijective. After any base change, the vertical maps remain bijective, so the
lifted component map is universally bijective as well. Its finiteness makes it
integral; universal injectivity and surjectivity then make it a universal
homeomorphism. Pullback associativity identifies these pieces with those in
the displayed statement. An empty partition transports to an empty partition;
an empty base admits the empty etale cover. No witness is chosen to define data
in another declaration: the entire conclusion is propositional existence. -/
theorem finite_splitting_descends_surjective_closedImmersion
    {X Y R : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (r : R ⟶ Y) [IsClosedImmersion r] [Surjective r] (U : Y.Opens)
    (h : ∃ 𝒯 : Cover.{u} etalePrecoverage (r ⁻¹ᵁ U).toScheme, ∀ i,
      ∃ (n : ℕ)
        (W : Fin n → (pullback (𝒯.f i) (pullback.snd f r ∣_ (r ⁻¹ᵁ U))).Opens),
        (⨆ j, W j) = ⊤ ∧ Pairwise (fun j k ↦ Disjoint (W j) (W k)) ∧
        ∀ j, IsUniversalHomeomorphism
          ((W j).ι ≫ pullback.fst (𝒯.f i) (pullback.snd f r ∣_ (r ⁻¹ᵁ U)))) :
    ∃ 𝒯 : Cover.{u} etalePrecoverage U.toScheme, ∀ i,
      ∃ (n : ℕ) (W : Fin n → (pullback (𝒯.f i) (f ∣_ U)).Opens),
        (⨆ j, W j) = ⊤ ∧ Pairwise (fun j k ↦ Disjoint (W j) (W k)) ∧
        ∀ j, IsUniversalHomeomorphism
          ((W j).ι ≫ pullback.fst (𝒯.f i) (f ∣_ U)) := by sorry

end AlgebraicGeometry.Scheme
