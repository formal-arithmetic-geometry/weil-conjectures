/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.AlgebraicGeometry.PhSchemeSite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# The affine standard-sieve basis of the ph topology

Source: Stacks Project, Topologies, Tags 0DBD, 0DBF, 0DBG, 0DBI, 0DBQ and 021N;
More on Morphisms, Tag 0DBT (blueprint: lem-trf-ph-affine-standard-sieve-basis).

The first clause is the sieve-basis criterion on affine objects: covering sieves contain
restrictions of a proper surjection to a finite affine open covering of its source.
The other clauses give affine locality, étale coverings, and Zariski coverings being étale.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The standard affine basis, affine locality, and étale comparison for the generated ph
topology. Finite covers are indexed by `Fin m`, including `m = 0`; arbitrary covering
families are small in the same larger universe as in `phTopology`.

Source: Stacks, Tags 0DBD, 0DBF, 0DBG, 0DBI, 0DBQ, 021N and 0DBT
(blueprint: lem-trf-ph-affine-standard-sieve-basis).

Proof plan:
1. Refine any open cover of a quasi-compact scheme by a finite affine open cover,
   retaining its factorizations through the original opens. Use
   lem-pc-fppf-affine-open-cover and lem-weil-pbc-affine-scheme-qcqs. Over an affine
   target, the identity proper surjection makes such a refinement standard.
2. Standard families are stable under affine base change: properness and surjectivity
   persist (lem-weil-pbc-proper-base-change and lem-weil-pbc-surjective-base-change),
   and the finite inverse-image cover is affine by
   lem-weil-pbc-fibre-product-affine-spectra.
3. Define an auxiliary collection of covering sieves by requiring every affine test
   pullback to contain a standard family. The identity family proves maximality,
   and composition of sieve pullbacks proves pullback stability.
4. For transitivity, first choose a standard family inside the first covering sieve,
   and then one on each of its affine domains inside the corresponding pullback
   of the second sieve. Apply lem-trf-standard-ph-composite-refinement; sieve closure
   puts every member of the standard refinement in the second sieve.
5. Every generator of phTopology belongs to the auxiliary topology. For a Zariski
   generator use step 1 after affine base change. For a proper-surjection generator,
   its pullback has quasi-compact source, so choose its finite affine open cover.
   Leastness of the generated topology gives the first inclusion.
6. Conversely, a standard family covers in phTopology: the proper-surjection
   generator followed by its Zariski open cover covers by transitivity. Upward
   closure follows from the topology axioms, since pullback of a larger sieve along
   a member of the smaller sieve is maximal.
7. Restrict an auxiliary covering sieve to an affine open covering of its target.
   Step 6 makes these restrictions ph covering, so Zariski transitivity proves the
   reverse inclusion. Testing the resulting equality at the identity of an affine
   target gives the first clause. The standard families have affine domains, are
   stable under affine pullback by step 2, and admit composite refinements by step 4:
   this is the induced affine sieve basis. Pullback stability and Zariski
   transitivity give exactly the affine-local criterion in the second clause.
8. Pull back an étale covering to an affine open, using
   lem-weil-pbc-etale-covering-base-change. It is fppf. Apply
   lem-trf-fppf-finite-surjective-refinement and lem-weil-pbc-finite-proper to obtain
   a proper surjection with an open covering subordinate to this family. Refine by
   finitely many affine opens using step 1; steps 6 and 7 prove it is ph covering.
9. A Zariski covering is jointly surjective by definition, and all its members are
   étale by lem-weil-pbc-open-immersion-etale, giving the last clause.
10. All covers and refinements lie in the fixed universe. For an empty affine target,
    take its identity proper surjection and the empty affine open cover. The empty
    Zariski cover makes every sieve cover there. For a nonempty target surjectivity
    rules out an empty standard covering. No finiteness is imposed on an affine
    open cover of an arbitrary, possibly non-quasi-compact target. -/
theorem ph_affine_standard_sieve_basis (S : Scheme.{u}) :
    (∀ (T : Over S), IsAffine T.left → ∀ (R : Sieve T),
      R ∈ phTopology S T ↔
        ∃ (W : Over S) (p : W ⟶ T),
          IsProper p.left ∧ Function.Surjective p.left ∧
          ∃ (m : ℕ) (U : Fin m → W.left.Opens),
            (∀ k, IsAffineOpen (U k)) ∧ (⨆ k, U k) = ⊤ ∧
            ∀ k, R ((Over.homMk (U k).ι :
              Over.mk ((U k).ι ≫ W.hom) ⟶ W) ≫ p)) ∧
    (∀ (T : Over S) (R : Sieve T) (I : Type (u + 1))
        (A : I → Over S) (a : ∀ i, A i ⟶ T),
      (∀ i, IsAffine (A i).left) → (∀ i, IsOpenImmersion (a i).left) →
      (∀ x : T.left, ∃ (i : I) (y : (A i).left), (a i).left y = x) →
      (R ∈ phTopology S T ↔ ∀ i, R.pullback (a i) ∈ phTopology S (A i))) ∧
    (∀ (T : Over S) (I : Type (u + 1)) (E : I → Over S) (e : ∀ i, E i ⟶ T),
      (∀ i, Etale (e i).left) →
      (∀ x : T.left, ∃ (i : I) (y : (E i).left), (e i).left y = x) →
      Sieve.generate (Presieve.ofArrows E e) ∈ phTopology S T) ∧
    (∀ (T : Over S) (I : Type (u + 1)) (U : I → Over S) (f : ∀ i, U i ⟶ T),
      (∀ i, IsOpenImmersion (f i).left) →
      (∀ x : T.left, ∃ (i : I) (y : (U i).left), (f i).left y = x) →
      ∀ i, Etale (f i).left) := by
  sorry

end AlgebraicGeometry.Scheme
