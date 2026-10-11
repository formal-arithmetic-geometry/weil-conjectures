/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Sheaf.Topology.RingedSpaceModuleCohomology
import Sheaf.CategoryTheory.SiteCechComplex

/-!
# Module cohomology vanishing from cofinal basis Čech coverings

Source: Stacks Project, Cohomology of Sheaves, Lemma 20.11.9, Tag 01EW,
with restriction to open subschemes as in Tag 01E1
(blueprint: lem-weil-pbc-module-cech-vanishing-basis).
-/

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- Higher module cohomology vanishes on a basis if higher Čech cohomology vanishes
for a cofinal collection of coverings whose members and finite nonempty intersections
belong to the basis. The type `K` indexes the collection `Cov`; `U c`, `V c`, and
`hom c` give its target, family of opens, and inclusion arrows. `S c` is any choice
of the iterated fibre products defining its Čech complex.

Source: Stacks Project, Cohomology of Sheaves, Lemma 20.11.9 (01EW), and 01E1
(blueprint: lem-weil-pbc-module-cech-vanishing-basis).

Proof:
1. Fix the basis and collection and induct on positive degree, simultaneously for
all modules with vanishing higher Čech cohomology on this collection.
2. Embed such a module G into an injective I, using
lem-weil-pbc-scheme-modules-enough-injectives and def-sp-injective-resolutions.
Take Q = I/G, giving a short exact sequence (def-weil-pbc-exact-sequence).
3. By lem-weil-pbc-module-injective-open-cover-cech-acyclic (01EP), I also has
vanishing higher Čech cohomology on every covering in the collection.
4. Kernels are sectionwise. On each basis open W, cofinality and the vanishing
of Čech H¹(G) give surjectivity I(W) → Q(W), by
lem-weil-pbc-module-ses-cech-h1-surjective (01EU).
5. All intersection opens of a covering belong to the basis. Thus products of
these section sequences give a short exact sequence of Čech complexes, using
functoriality of def-weil-pbc-site-cech-complex and
lem-weil-pbc-cochain-complexes-degreewise-exact.
6. Its long exact cohomology sequence (lem-weil-pbc-complex-ses-homology-long-exact)
and the vanishing for G and I show that Q has the same Čech vanishing property.
7. Restriction to an open is exact and preserves injectives, by
lem-weil-pbc-module-open-restriction-injectives. Its sections are the original
sections by lem-weil-pbc-module-restriction-open-immersion-colimits (01E1).
8. Compute module cohomology on the open subscheme as right derived global sections
(pqf-def-cohomology, def-sp-left-exact-additive), with enough injectives there.
9. Use lem-weil-pbc-derived-functor-long-exact and
lem-weil-pbc-derived-functor-injective-vanishing. In degree one, surjectivity on
sections and lem-weil-pbc-right-derived-universal-delta-functor give vanishing.
In degree p ≥ 2, apply the induction hypothesis to Q in degree p-1 and shift
along the long exact sequence. Apply this result to F. -/
theorem isZero_moduleCohomology_restrict_of_cech_basis
    (X : Scheme.{u}) (F : X.Modules) (B : Set X.Opens)
    (hB : IsTopologicalBasis ((fun W : X.Opens => (W : Set X)) '' B))
    (K : Type w) (J : K → Type (max u v)) (U : K → X.Opens)
    (V : ∀ c : K, J c → X.Opens) (hom : ∀ (c : K) (j : J c), V c j ⟶ U c)
    (S : ∀ c : K, SiteCechComplex (V c) (hom c))
    (hcover : ∀ c : K, iSup (V c) = U c)
    (hbase : ∀ c : K, U c ∈ B ∧ (∀ j : J c, V c j ∈ B) ∧
      ∀ (p : ℕ) (t : Fin (p + 1) → J c), (⨅ k, V c (t k)) ∈ B)
    (hcofinal : ∀ (W : X.Opens), W ∈ B →
      ∀ (A : Type (max u v)) (Z : A → X.Opens), iSup Z = W →
        ∃ c : K, U c = W ∧ ∀ j : J c, ∃ a : A, V c j ≤ Z a)
    (hvanish : ∀ (c : K) (p : ℕ), 0 < p →
      IsZero (((S c).cohomologyFunctor p).obj F.val.presheaf)) :
    ∀ (p : ℕ), 0 < p → ∀ W : X.Opens, W ∈ B →
      IsZero ((RingedSpace.moduleCohomology W.toScheme.toRingedSpace p).obj
        ((restrictFunctor W.ι).obj F)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
