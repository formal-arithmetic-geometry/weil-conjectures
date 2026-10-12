/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.EtaleLocalFiniteMultiplePointsElementary
import Sheaf.AlgebraicGeometry.FinitePiecePersistence

/-!
# Splitting off isolated fibre points in an elementary étale neighbourhood

Source: Stacks Project, More on Morphisms, Lemma 37.41.4, Tag 02LN
(blueprint: lem-weil-pbc-etale-splits-off-isolated-points-technical).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Source: Stacks Project, More on Morphisms, Tag 02LN
(blueprint: lem-weil-pbc-etale-splits-off-isolated-points-technical).
A separated locally finite type morphism splits off finite disjoint open pieces through any
finite family of distinct isolated fibre points after an elementary étale base change.

Proof: For `n = 0`, use the identity neighbourhood and the whole pullback as `W`.
Otherwise apply `lem-weil-pbc-etale-local-finite-multiple-points-elementary` (Tag 02LL)
to obtain the elementary neighbourhood and finite open pieces with their unique fibre points
and residue-field isomorphisms. By `lem-weil-pbc-separated-base-change` the base-changed
morphism is separated. Each finite piece is proper by
`lem-weil-pbc-finite-morphism-permanence`; its inclusion is proper by
`lem-weil-pbc-proper-over-separated` and closed by `lem-weil-pbc-proper-immersion-closed`.
Pairwise intersections are closed in the finite pieces; their images in the base are closed
and avoid the distinguished point, since the original points are distinct. Remove these
finitely many images from the base. The retained properties follow from
`lem-weil-pbc-elementary-etale-finite-piece-persistence`, and étaleness from
`lem-weil-pbc-etale-composition-cancellation`. The pieces are now disjoint; their complement
is the open and closed `W`. Finally `lem-weil-pbc-fibre-product-points` identifies points above
`(x i, t)` with primes of the residue-field tensor product. Since the neighbourhood has
trivial residue extension, this tensor product is a field with a unique prime. Thus a point
in `W` above this pair would equal the selected point of `V i`, contradicting disjointness. -/
theorem exists_etale_splits_off_isolated_points
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [IsSeparated f]
    (s : S) (n : ℕ) (x : Fin n → X) (h_distinct : Function.Injective x)
    (h_over : ∀ i : Fin n, f (x i) = s)
    (h_isolated : ∀ i : Fin n, IsOpen ({f.asFiber (x i)} : Set (f.fiber (f (x i))))) :
    ∃ (U : Scheme.{u}) (φ : U ⟶ S) (t : U),
      Etale φ ∧ φ t = s ∧ IsIso (φ.residueFieldMap t) ∧
      ∃ (W : (pullback φ f).Opens) (V : Fin n → (pullback φ f).Opens),
        (∀ i : Fin n, Disjoint W (V i)) ∧
        (∀ i j : Fin n, i ≠ j → Disjoint (V i) (V j)) ∧
        W ⊔ (⨆ i : Fin n, V i) = ⊤ ∧
        (∀ i : Fin n, IsFinite ((V i).ι ≫ pullback.fst φ f)) ∧
        (∀ i : Fin n, ∃ v : (V i).toScheme,
          ((V i).ι ≫ pullback.fst φ f) v = t ∧
          (∀ v' : (V i).toScheme, ((V i).ι ≫ pullback.fst φ f) v' = t → v' = v) ∧
          ((V i).ι ≫ pullback.snd φ f) v = x i ∧
          IsIso (((V i).ι ≫ pullback.snd φ f).residueFieldMap v)) ∧
        (∀ w : W.toScheme, (W.ι ≫ pullback.fst φ f) w = t →
          ∀ i : Fin n, (W.ι ≫ pullback.snd φ f) w ≠ x i) := by
  sorry

end AlgebraicGeometry
