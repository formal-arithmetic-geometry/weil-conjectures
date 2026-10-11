/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Sheaf.AlgebraicGeometry.FiberDegreeBound
import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Topology.Basic

/-!
# Stratification of flat finitely presented locally quasi-finite morphisms

Source: Stacks Project, More on Morphisms, Lemma Tag 07RY
(blueprint: lem-weil-pbc-flat-fp-lqf-bounded-stratification).

As in `Sheaf.AlgebraicGeometry.FlatQuasiFiniteStratification`, the closed filtration is
indexed from zero: `Z 0` is the paper's `Z_{-1} = ∅` and `Z (r + 1)` is the paper's `Z_r`,
so the degree-`r` stratum is `Z (r + 1) \ Z r`, written out in place. The bound `n` is the
one supplied by the hypothesis `BoundsFiberDegrees f n`, and `Z (n + 1) = Set.univ`.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

/-- Flat, locally finitely presented, separated, locally quasi-finite morphisms with universally
bounded fibres are finite locally free on a finite stratification (Stacks, Tag 07RY;
(blueprint: lem-weil-pbc-flat-fp-lqf-bounded-stratification).

Proof (Stacks Tag 07RY, following the ten steps of the DAG node):
1. Choose a bound on fibre degrees. Base change preserves flatness, local finite presentation,
   separatedness and local quasi-finiteness, and preserves each fibre degree
   (`lem-weil-pbc-flat-morphism-base-change`, `lem-weil-pbc-qcqs-morphism-permanence`,
   `lem-weil-pbc-separated-lqf-base-change`, `lem-weil-pbc-fibre-degree-base-change`).
2. For a point of maximal degree `m`, use an elementary étale neighbourhood to split the
   pullback into a finite part `V` and an open part `W` with empty fibre at that point
   (`lem-weil-pbc-finite-closed-map-finite-fibres`, `def-pc-scheme-fibre`,
   `lem-weil-pbc-etale-splits-off-quasi-finite-part`).
3. The finite part is flat and locally of finite presentation by restriction to an open,
   hence finite locally free (`def-pc-finite-locally-free`).
4. Shrink the neighbourhood so that `V` has constant degree. Its degree is `m` because the
   fibre of `W` at the chosen point is empty (
   `lem-weil-pbc-finite-locally-free-degree-locally-constant`,
   `lem-weil-pbc-open-preimage-fibre-product`,
   `lem-weil-pbc-etale-composition-cancellation`, `lem-weil-pbc-fibre-degree-base-change`).
5. Additivity of degrees on the disjoint open parts and the bound `m` force every fibre of
   `W` to be empty. Thus `W` is empty and the image of the neighbourhood is in the degree-`m`
   locus. Étale maps are open, so this locus is open (`lem-weil-pbc-etale-morphism-open-map`).
6. Factor the neighbourhood maps through that open locus and descend finite local freeness
   of degree `m` along this étale cover (`lem-weil-pbc-morphism-factors-through-open-subscheme`,
   `lem-weil-pbc-finite-locally-free-degree-etale-descent`). This proves the maximal-degree claim.
7. Put `Z (r + 1) = {s | the fibre degree at s is at most r}` and `Z 0 = ∅`. Induct on the
   bound: for bound zero these are the whole base; otherwise the complement of the
   maximal-degree locus is closed.
   Give it the reduced induced closed subscheme structure and apply induction to the pullback,
   whose bound is one smaller (`lem-weil-pbc-reduced-induced-closed-subscheme`,
   `lem-weil-pbc-fibre-degree-base-change`). The closed immersion makes all `Z r` closed in `S`.
8. Successive differences are precisely the degree loci, hence disjoint and cover `S`;
   degree loci above the bound `n` are empty since `Z r = Set.univ` for `r ≥ n + 1`.
9. If a base change is finite locally free of degree `r`, fibre-degree invariance puts every
   image point in the degree-`r` stratum (`lem-weil-pbc-fibre-degree-base-change`).
10. Conversely, if the image lies in that stratum, every fibre of the base change has degree
    `r`. Apply the maximal-degree claim to that base change with bound `r` to obtain finite
    local freeness of degree `r`, including the empty-base case.
-/
theorem exists_flat_fp_lqf_bounded_stratification {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] [IsSeparated f]
    (h_lqf : IsLocallyQuasiFinite f) (n : ℕ) (hn : BoundsFiberDegrees f n) :
    ∃ Z : ℕ → Set S,
      Z 0 = ∅ ∧ (∀ r : ℕ, IsClosed (Z r)) ∧ Monotone Z ∧ Z (n + 1) = Set.univ ∧
      Pairwise (fun r t : ℕ => Disjoint (Z (r + 1) \ Z r) (Z (t + 1) \ Z t)) ∧
      (⋃ r : ℕ, Z (r + 1) \ Z r) = Set.univ ∧
      (∀ (T : Scheme.{u}) (g : T ⟶ S) (r : ℕ),
        (pullback.snd f g).IsFiniteLocallyFreeOfDegree r ↔ Set.range g ⊆ Z (r + 1) \ Z r) := by
  sorry

end AlgebraicGeometry.Scheme.Hom
