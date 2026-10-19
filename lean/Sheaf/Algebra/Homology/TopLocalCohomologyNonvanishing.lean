/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q46
-/
module

public import WeilConjectures.Algebra.Homology.IdealPowerTorsionFunctor
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.Topology.KrullDimension
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.KrullDimension.Basic
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Sheaf.RingTheory.CompletionDimension
import Sheaf.RingTheory.CohenPowerSeriesPresentation
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses

/-! # Nonvanishing of top local cohomology

Source: Stacks Project, Local Cohomology, Tag 0DXE (lemma-cd-maximal),
top-degree nonvanishing (blueprint: lem-per-local-cohomology-top-nonvanishing).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- Top local cohomology of a nonzero Noetherian local ring is nonzero.
The maximal ideal is the unique maximal ideal, and local cohomology is the right
derived functor of the ideal-power torsion functor, evaluated on the ring itself.
Source: Stacks Project, Local Cohomology, Tag 0DXE (lemma-cd-maximal)
(blueprint: lem-per-local-cohomology-top-nonvanishing).

Proof:
1. Pass to A, the maximal-ideal completion of R. It is Noetherian and local with
   maximal ideal nA and the same residue field and dimension d. The map R → A is
   flat. Completeness of module completion, and (nA)^k = n^k A, make A complete
   for its own maximal ideal. These use def-weil-pbc-adic-completion,
   lem-weil-pbc-adic-completion-noetherian, lem-weil-pbc-local-completion-local-ring,
   lem-weil-pbc-completion-dimension, lem-weil-pbc-local-completion-faithfully-flat,
   and lem-weil-pbc-module-completion-complete.
2. A Cohen presentation (lem-weil-pbc-cohen-power-series-presentation) gives a
   surjection S → A from a complete regular local ring. By
   lem-trf-regular-local-bounded-injective-resolution, S[0] has a bounded injective
   representative J, which is K-injective by
   lem-weil-pbc-bounded-below-injectives-kinjective. Evaluation at 1 identifies
   Hom(S[0],J) with J, so its scalar-action map is an isomorphism, using
   def-pur-derived-internal-hom.
3. Since A is finite over S, lem-trf-finite-map-dualizing-transfer gives a
   dualizing complex over A. Apply lem-per-algebraic-local-dualizing-normalization
   to obtain a normalized dualizing complex omega, in the sense of
   def-per-algebraic-normalized-dualizing. Its cohomology modules are finite.
4. A maximal-length prime chain in A has length d, and its first prime p is minimal:
   a smaller prime would extend the chain. Prime correspondence for A/p shows
   dim(A/p) = d, also when d = 0 (def-weil-pbc-krull-dimension-ring).
5. By lem-per-algebraic-dualizing-generic-degree, H^(-d)(omega) localized at p
   is nonzero. Thus N = H^(-d)(omega) is a nonzero finite A-module.
6. Apply lem-per-algebraic-local-duality with M = A and i = d. Evaluation at 1
   identifies RHom(A[0],omega) with omega. The resulting isomorphism identifies
   the completion of N with Hom(H^d_(nA)(A),E), where E is the residue-field
   injective hull. By lem-weil-pbc-completion-finite-module-tensor and the
   completeness of A, this completion is A tensor_A N, hence N, and is nonzero.
   Therefore H^d_(nA)(A) is nonzero.
7. By lem-per-local-cohomology-flat-base-change,
   H^d_n(R) tensor_R A is isomorphic to H^d_(nA)(A). A zero module has zero
   tensor product, so the latter nonvanishing forces H^d_n(R) to be nonzero. -/
theorem top_local_cohomology_nonzero
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (d : ℕ)
    (hd : topologicalKrullDim (AlgebraicGeometry.Spec (.of R)) = (d : WithBot ℕ∞)) :
    ¬ IsZero (((idealPowerTorsion (IsLocalRing.maximalIdeal R)).rightDerived d).obj
      (ModuleCat.of R R)) := by
  sorry

end ModuleCat
