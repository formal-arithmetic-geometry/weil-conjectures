/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.Topology.Constructible
import Sheaf.AlgebraicGeometry.EtaleSeparatedStratifiedFinite
import Sheaf.AlgebraicGeometry.ImmersionAffineConstructiblePieces
import Sheaf.AlgebraicGeometry.SeparatedAffineCoverCriterion
import WeilConjectures.ConstructibleSheaf.Refinement

/-!
# Stratifying an etale affine cover and its overlaps

Source: Stacks Project, Etale Cohomology, `lemma-etale-stratified-finite`, proof,
second paragraph (blueprint: lem-weil-pbc-etale-affine-cover-gluing).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite affine open cover of a qcqs etale scheme over an affine base admits a
finite partition of the base into constructible locally closed affine subschemes on
which the charts and their overlaps are finite etale and the whole scheme is separated.
Source: Stacks Project, Etale Cohomology, `lemma-etale-stratified-finite`, proof,
second paragraph (blueprint: lem-weil-pbc-etale-affine-cover-gluing).

Proof:
1. Each affine chart and each overlap is separated, quasi-compact and etale over the
   affine base: use affine-morphism permanence, separated cancellation, qcqs permanence,
   and etale composition (`lem-weil-pbc-affine-morphism-permanence`,
   `lem-weil-pbc-separated-cancellation`, `lem-weil-pbc-qcqs-morphism-permanence`,
   `lem-weil-pbc-proper-fp-permanence`, `lem-weil-pbc-etale-composition-cancellation`).
2. Apply `lem-weil-pbc-etale-separated-stratified-finite` to each chart and overlap.
3. Take a common refinement (`lemma-constructible-common-refinement`); its images are
   finite intersections of constructible locally closed sets, and finite etaleness
   persists by base change (`def-weil-pbc-finite-etale-category`, `def-pc-fibre-product`).
4. Refine into affine pieces with `lem-weil-pbc-immersion-affine-constructible-pieces`.
   Again finite etaleness persists by base change.
5. Identify the pulled-back charts and overlaps with opens of the pulled-back scheme
   (`lem-weil-pbc-open-fibre-product`). Finite morphisms over the affine stratum make
   them affine, proper and separated (`lem-weil-pbc-finite-morphism-permanence`,
   `lem-weil-pbc-affine-morphism-permanence`, `lem-weil-pbc-proper-fp-permanence`).
6. Each overlap inclusion into a chart is proper by
   `lem-weil-pbc-proper-over-separated`, and hence a closed immersion by
   `lem-weil-pbc-proper-immersion-closed`. Its restriction on sections is surjective
   (`lem-weil-pbc-closed-immersion-affine-cover-criterion`); consequently the map from
   the tensor product of the sections of the two charts is surjective as well.
7. Apply `lem-weil-pbc-separated-affine-cover-criterion` to conclude separatedness. -/
theorem exists_etale_affine_cover_stratification
    {X U : Scheme.{u}} [IsAffine X] [CompactSpace U] [QuasiSeparatedSpace U]
    (j : U ⟶ X) [Etale j] (m : ℕ) (A : Fin m → U.Opens)
    (hA : ∀ a : Fin m, IsAffineOpen (A a)) (hcover : ⨆ a : Fin m, A a = ⊤) :
    ∃ (n : ℕ) (S : Fin n → Scheme.{u}) (ι : ∀ i : Fin n, S i ⟶ X),
      (∀ i : Fin n, IsAffine (S i) ∧ IsImmersion (ι i) ∧
        Topology.IsConstructible (Set.range (ι i))) ∧
      Pairwise (fun i k : Fin n ↦ Disjoint (Set.range (ι i)) (Set.range (ι k))) ∧
      (⋃ i : Fin n, Set.range (ι i)) = Set.univ ∧
      (∀ (i : Fin n) (a : Fin m),
        IsFinite (pullback.snd ((A a).ι ≫ j) (ι i)) ∧
        Etale (pullback.snd ((A a).ι ≫ j) (ι i))) ∧
      (∀ (i : Fin n) (a b : Fin m),
        IsFinite (pullback.snd ((A a ⊓ A b).ι ≫ j) (ι i)) ∧
        Etale (pullback.snd ((A a ⊓ A b).ι ≫ j) (ι i))) ∧
      (∀ i : Fin n, IsSeparated (pullback.snd j (ι i))) := by
  sorry

end AlgebraicGeometry
