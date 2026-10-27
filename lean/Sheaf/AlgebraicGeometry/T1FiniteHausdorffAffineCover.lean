/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Sheaf.AlgebraicGeometry.ZeroDimensionalSpectrumProfinite

/-!
# Finite compact Hausdorff affine charts for schemes with closed points

Source: Stacks Project, Properties, Tag 0CKV, `lemma-dimension-zero`, opening proof
paragraph and the finite affine covering in the final paragraph
(blueprint: lem-sfb-t1-finite-hausdorff-affine-cover).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A quasi-compact scheme with closed points has a finite affine open cover by
compact Hausdorff charts, with specified spectrum presentations whose primes are maximal.
The index `Fin n` permits the empty cover, and each chart carries its subspace topology.
Source: Stacks Project, Properties, Tag 0CKV, `lemma-dimension-zero`, opening proof
paragraph and the finite affine covering in the final paragraph
(blueprint: lem-sfb-t1-finite-hausdorff-affine-cover).

Proof:
1. Apply `lem-weil-pbc-qcqs-finite-affine-open-cover` to obtain finitely many affine
   opens covering `X`. Enumerate them by `Fin n` and, using `def-pc-scheme`, choose
   commutative rings `A i` and scheme isomorphisms `(U i).toScheme ≅ Spec (A i)`.
   If `X` is empty, take `n = 0`.
2. Closedness of singletons restricts from `X` to each open subspace `U i`, and the
   underlying homeomorphism of its spectrum presentation carries this to `Spec (A i)`.
3. For a prime `p` of `A i`, `lem-weil-pbc-spec-irreducible-closed-subsets-primes`
   identifies its closure with `V(p)`, hence `V(p) = {p}`. By
   `lem-weil-pbc-proper-ideal-contained-in-maximal`, choose a maximal ideal `m`
   containing `p`. To see that `m` is prime, if `ab ∈ m` and `a ∉ m`, write
   `1 = c + ra` with `c ∈ m` and multiply by `b` to get `b ∈ m`.
   Thus `m ∈ V(p) = {p}`, so `p = m` is maximal.
4. Apply `lem-weil-pbc-zero-dimensional-spectrum-profinite` to `A i`.
   Transport its quasi-compactness and Hausdorffness to `U i` along the homeomorphism:
   an open cover gives a finite subcover, and distinct points have disjoint open
   neighbourhoods. No property of the intersections of the charts is used. -/
theorem Scheme.exists_finite_hausdorff_affine_cover (X : Scheme.{u})
    [CompactSpace X] [T1Space X] :
    ∃ (n : ℕ) (U : Fin n → X.Opens) (A : Fin n → CommRingCat.{u}),
      (∀ i : Fin n, IsAffineOpen (U i)) ∧
      (∀ i : Fin n, Nonempty ((U i).toScheme ≅ Spec (A i))) ∧
      (⨆ i : Fin n, U i) = ⊤ ∧
      (∀ (i : Fin n) (p : Ideal (A i)), p.IsPrime → p.IsMaximal) ∧
      (∀ i : Fin n, CompactSpace (U i)) ∧
      (∀ i : Fin n, T2Space (U i)) := by
  classical
  obtain ⟨s, hs, hcover⟩ :=
    (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : X.Opens))).mp
      isCompact_univ
  let := hs.fintype
  let e := Fintype.equivFin s
  let U (i : Fin (Fintype.card s)) : X.Opens := (e.symm i).val.val
  have hU (i) : IsAffineOpen (U i) := (e.symm i).val.property
  let A (i : Fin (Fintype.card s)) : CommRingCat.{u} := Γ(X, U i)
  have hiso (i) : (U i).toScheme ≅ Spec (A i) := (hU i).isoSpec
  have hmax (i) (p : Ideal (A i)) (hp : p.IsPrime) : p.IsMaximal := by
    let : T1Space (U i).toScheme := by
      change T1Space { x : X // x ∈ U i }
      infer_instance
    let : T1Space (PrimeSpectrum (A i)) := by
      change T1Space (Spec (A i))
      exact (hiso i).hom.homeomorph.t1Space
    exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal ⟨p, hp⟩).mp
      (isClosed_singleton : IsClosed ({⟨p, hp⟩} : Set (PrimeSpectrum (A i))))
  refine ⟨Fintype.card s, U, A, hU, fun i ↦ ⟨hiso i⟩, ?_, hmax, ?_, ?_⟩
  · rw [hcover]
    apply le_antisymm
    · refine iSup_le fun i ↦ ?_
      exact le_iSup_of_le (e.symm i).val (le_iSup_of_le (e.symm i).property le_rfl)
    · refine iSup_le fun j ↦ iSup_le fun hj ↦ ?_
      exact le_iSup_of_le (e ⟨j, hj⟩) (by simp [U])
  · intro i
    let := (Spec.profinite_of_isMaximal (A i) (hmax i)).1
    exact (hiso i).hom.homeomorph.symm.compactSpace
  · intro i
    let := (Spec.profinite_of_isMaximal (A i) (hmax i)).2.1
    exact (hiso i).hom.homeomorph.symm.t2Space

end AlgebraicGeometry
