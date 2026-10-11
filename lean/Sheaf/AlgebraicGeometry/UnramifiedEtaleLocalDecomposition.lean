/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Étale-local decomposition near unramified fibre points

Source: Stacks Project, Étale Morphisms, Lemma 41.17.2, Tag 04HI
(blueprint: lem-weil-pbc-unramified-etale-local-decomposition).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Stacks Project, Étale Morphisms, Lemma 41.17.2 (Tag 04HI)
(blueprint: lem-weil-pbc-unramified-etale-local-decomposition).
A separated morphism unramified at finitely many points over `s` admits an étale
neighbourhood with a clopen decomposition into closed immersions through the chosen point
and a remainder whose fibre contains no point mapping to a listed point. The finite family
is indexed by pairs `(i,j)` with `i : Fin n` and `j : Fin (m i)`. Opens specify their actual
open subschemes via `Scheme.Opens.toScheme`; disjointness and covering give the disjoint
union decomposition. No residue-field isomorphism is required of the étale neighbourhood.

Proof:
1. Choose unramified open neighbourhoods of the listed points and take their finite union.
   Use `lem-weil-pbc-unramified-fibre-point-isolated` and
   `lem-weil-pbc-etale-local-finite-multiple-points` to obtain finite open pieces after an
   étale base change. Unramifiedness persists by
   `lem-weil-pbc-unramified-base-change-open` (Stacks 02G6 and 02GA).
2. Shrink the neighbourhood to an affine open, using
   `lem-weil-pbc-etale-composition-cancellation`. Apply
   `lem-weil-pbc-finite-unramified-one-point-closed` to the finite unramified pieces and
   intersect the resulting neighbourhoods. On each shrinking replace every piece by its
   base change; `lem-weil-pbc-open-fibre-product` identifies it with the inverse-image open.
3. The pullback is separated. Each piece is proper over the base, so
   `lem-weil-pbc-proper-over-separated` makes its inclusion closed. Intersections of pairs
   of pieces have closed images in the base avoiding the chosen point, by the exclusion
   in `lem-weil-pbc-etale-local-finite-multiple-points`.
4. Delete these finitely many images and base change the pieces again, using
   `lem-weil-pbc-open-fibre-product`. They are now disjoint and clopen. Their clopen
   complement is the remainder, with the required exclusion. If the listed points exhaust
   the original fibre, the remainder's fibre is empty. -/
theorem exists_etale_closed_immersion_decomposition_of_unramified_at_points
    {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] (s : S)
    (n : ℕ) (x : Fin n → X) (hx : ∀ i, f.base (x i) = s)
    (hunramified : ∀ i, ∃ O : X.Opens, x i ∈ O ∧
      LocallyOfFiniteType (O.ι ≫ f) ∧ IsOpenImmersion (pullback.diagonal (O.ι ≫ f))) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S) (u : U),
      Etale g ∧ g.base u = s ∧
      ∃ (m : Fin n → ℕ) (W : (pullback f g).Opens)
        (V : (Σ i : Fin n, Fin (m i)) → (pullback f g).Opens),
        IsClosed (W : Set ↥(pullback f g)) ∧
        (∀ a, IsClosed (V a : Set ↥(pullback f g))) ∧
        Pairwise (fun a b ↦ Disjoint (V a) (V b)) ∧
        (∀ a, Disjoint W (V a)) ∧
        W ⊔ iSup V = ⊤ ∧
        (∀ a, IsClosedImmersion ((V a).ι ≫ pullback.snd f g) ∧
          u ∈ Set.range (((V a).ι ≫ pullback.snd f g).base)) ∧
        (∀ p : ↥(pullback f g), p ∈ W → (pullback.snd f g).base p = u →
          ∀ i, (pullback.fst f g).base p ≠ x i) ∧
        ((∀ y : X, f.base y = s ↔ ∃ i, y = x i) →
          ∀ p : ↥(pullback f g), p ∈ W → (pullback.snd f g).base p ≠ u) := by
  sorry

end AlgebraicGeometry
