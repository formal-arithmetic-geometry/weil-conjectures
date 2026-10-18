/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Sheaf.AlgebraicGeometry.GroupoidScheme
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeDegreeLocallyConstant
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Invariant constant-rank strata of an affine groupoid scheme

Source: Stacks Project, Groupoid Schemes, Tag 03BI,
lemma-finite-locally-free-disjoint-free, and the first paragraph of
lemma-integral-over-invariants (blueprint: lem-a1-affine-groupoid-invariant-rank-strata).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite locally free affine groupoid has finitely many nonempty, invariant, affine
clopen rank strata of positive degree. All five structure maps restrict to each stratum.
Source: Stacks Project, Groupoid Schemes, Tag 03BI,
lemma-finite-locally-free-disjoint-free and the beginning of lemma-integral-over-invariants
(blueprint: lem-a1-affine-groupoid-invariant-rank-strata).

Proof plan, following the node's seven steps:
1. Apply `lem-weil-pbc-finite-locally-free-degree-locally-constant` to `s` to obtain its
   clopen degree strata and finite locally free restrictions.
2. The identity section gives a residue-field point in every source fibre. Evaluation
   splits its scalar inclusion, so its coordinate algebra has dimension at least one.
   This excludes the degree-zero stratum, using `def-pc-finite-locally-free`.
3. Write `P = R ×[s,U,t] R` and `Q = R ×[s,U,s] R`. The morphisms
   `(a,b) ↦ (c(a,b),b)` and `(d,b) ↦ (c(d,i(b)),b)` are inverse over `R` by the groupoid
   laws. Their existence follows from `def-pc-fibre-product`.
4. Base-change rank invariance (`lem-weil-pbc-finite-flat-rank-iso`, clause 2) identifies
   the ranks of these two projections with the ranks of `s` at `t(z)` and `s(z)`.
   Their isomorphism makes the ranks equal, hence the strata invariant.
5. Quasi-compactness (`lem-weil-pbc-affine-scheme-qcqs`) leaves finitely many nonempty
   disjoint strata. The empty object scheme has no such strata.
6. Clopen subsets of spectra are principal opens of idempotents
   (`lem-weil-pbc-spec-clopen-idempotent`); those opens are affine by clause 0 of
   `lem-weil-pbc-affine-ideals-closed-subscheme`. Apply this to both object and arrow schemes.
7. The identity, inverse, and composition factor through the invariant open subschemes
   (`def-weil-open-immersion`); their laws restrict. The inverse identifies the two
   restricted structure morphisms, giving both degree `r` in the sense of
   `def-pc-finite-locally-free`.
-/
theorem affineGroupoid_exists_invariant_rank_strata
    {A B : CommRingCat.{u}} (s t : Spec B ⟶ Spec A) (e : Spec A ⟶ Spec B)
    (i : Spec B ⟶ Spec B) (c : pullback s t ⟶ Spec B)
    (hG : IsGroupoidScheme s t e i c) [s.IsFiniteLocallyFree] [t.IsFiniteLocallyFree] :
    ∃ (I : Finset ℕ) (U : I → (Spec A).Opens) (V : I → (Spec B).Opens),
      (∀ r : I, 0 < r.1) ∧
      (∀ r : I, Nonempty (U r).toScheme ∧ IsClosed (U r : Set (Spec A)) ∧
        IsAffine (U r).toScheme) ∧
      Pairwise (fun r r' : I ↦ Disjoint (U r) (U r')) ∧
      (⨆ r : I, U r) = ⊤ ∧
      (IsEmpty (Spec A) → I = ∅) ∧
      ∀ r : I, V r = s ⁻¹ᵁ U r ∧ V r = t ⁻¹ᵁ U r ∧ IsAffine (V r).toScheme ∧
        ∃ (s' t' : (V r).toScheme ⟶ (U r).toScheme)
          (e' : (U r).toScheme ⟶ (V r).toScheme)
          (i' : (V r).toScheme ⟶ (V r).toScheme)
          (c' : pullback s' t' ⟶ (V r).toScheme)
          (k : pullback s' t' ⟶ pullback s t),
          IsGroupoidScheme s' t' e' i' c' ∧
          s'.IsFiniteLocallyFreeOfDegree r.1 ∧ t'.IsFiniteLocallyFreeOfDegree r.1 ∧
          s' ≫ (U r).ι = (V r).ι ≫ s ∧ t' ≫ (U r).ι = (V r).ι ≫ t ∧
          e' ≫ (V r).ι = (U r).ι ≫ e ∧ i' ≫ (V r).ι = (V r).ι ≫ i ∧
          k ≫ pullback.fst s t = pullback.fst s' t' ≫ (V r).ι ∧
          k ≫ pullback.snd s t = pullback.snd s' t' ≫ (V r).ι ∧
          c' ≫ (V r).ι = k ≫ c := by
  sorry

end AlgebraicGeometry
