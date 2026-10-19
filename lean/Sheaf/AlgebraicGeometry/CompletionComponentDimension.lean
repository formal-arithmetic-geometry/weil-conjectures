/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.KrullDimension
public import Sheaf.RingTheory.ExcellentRing
import Sheaf.RingTheory.LocalCompletionQuotient
import Sheaf.RingTheory.CompletionDimension
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Sheaf.RingTheory.RatliffFormalCatenarity

/-!
# One-dimensional components and completion

Source: Illusie–Laszlo–Orgogozo, Travaux de Gabber, Exposé XIV, Lemma 2.1.6
(completion preserves dimension-one components; converse under universal catenarity)
(blueprint: lem-per-completion-component-dimension).
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u

open AlgebraicGeometry

namespace AlgebraicGeometry

/--
Source: Illusie–Laszlo–Orgogozo, Travaux de Gabber, Exposé XIV, Lemma 2.1.6
(blueprint: lem-per-completion-component-dimension).

Proof, following the six DAG steps:
1. Put `B = Â`. For each minimal prime `p` of `A`, the ring `A / p` is a
   Noetherian local domain. The completion/quotient comparison identifies its
   completion `C_p` with `B / pB` (`lem-weil-pbc-local-completion-quotient`).
   Completion is Noetherian (`lem-weil-pbc-adic-completion-noetherian`), local
   (`lem-weil-pbc-local-completion-local-ring`) and faithfully flat
   (`lem-weil-pbc-local-completion-faithfully-flat`).
2. Flat going down (`lem-sc-flat-going-down`) shows that a minimal prime `q` of `B`
   contracts to a minimal
   prime `p` of `A`. The prime `q / pB` is minimal in `C_p`.
3. Conversely a minimal prime of `C_p` contracts to zero in `A / p` by going down.
   Lift it to `q` in `B` and choose a minimal prime `q₀` below it
   (`lem-weil-pbc-prime-contains-minimal-prime`). Its contraction
   is `p`, so `pB ≤ q₀`; minimality in `C_p` forces `q₀ = q`. Thus the components
   of the various `Spec C_p` are precisely the components of `Spec B`
   (`lem-weil-pbc-spec-irreducible-components-minimal-primes`).
4. Inverse images identify primes of a quotient with primes containing the ideal,
   preserving inclusion and closed sets. Hence `Spec (R / I)` is homeomorphic to
   `V(I)`, and a component associated to `p` has dimension `dim (R / p)`
   (`lem-weil-pbc-spec-topological-krull-dimension-ring`).
5. If `V(p)` has dimension one, completion preserves the dimension of `A / p`
   (`lem-weil-pbc-completion-dimension`).
   A minimal prime of the one-dimensional local ring `C_p` is strictly below its
   maximal ideal: equality would make every prime equal and give dimension zero.
   Its quotient therefore has dimension exactly one. Step 3 gives the desired
   component of `Spec B`, without any catenarity assumption.
6. For the converse, contract a minimal prime defining a dimension-one component
   of `Spec B`. Ratliff's criterion (`lem-per-ratliff-formal-catenarity`) makes `Spec C_p`
   equidimensional, so all its components have dimension one. Every finite prime
   chain lies above a minimal prime, so `C_p` itself has dimension one.
   Completion dimension equality then gives `dim (A / p) = 1`, as required.
-/
theorem completion_component_dimension
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] :
    ((∃ Z : Set (Spec (CommRingCat.of A)),
          Z ∈ irreducibleComponents (Spec (CommRingCat.of A)) ∧
            topologicalKrullDim Z = (1 : WithBot ℕ∞)) →
        ∃ Z : Set (Spec (CommRingCat.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))),
          Z ∈ irreducibleComponents
              (Spec (CommRingCat.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))) ∧
            topologicalKrullDim Z = (1 : WithBot ℕ∞)) ∧
      (IsUniversallyCatenary A →
        ((∃ Z : Set (Spec (CommRingCat.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))),
            Z ∈ irreducibleComponents
                (Spec (CommRingCat.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))) ∧
              topologicalKrullDim Z = (1 : WithBot ℕ∞)) →
          ∃ Z : Set (Spec (CommRingCat.of A)),
            Z ∈ irreducibleComponents (Spec (CommRingCat.of A)) ∧
              topologicalKrullDim Z = (1 : WithBot ℕ∞))) := by
  sorry

end AlgebraicGeometry
