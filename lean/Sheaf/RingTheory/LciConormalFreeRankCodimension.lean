/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.RingTheory.CompleteIntersectionOverField
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
import Sheaf.AlgebraicGeometry.GlobalCompleteIntersectionEquidimensional
import Sheaf.RingTheory.ConormalModulePrincipalLocalization
import Sheaf.RingTheory.GlobalCompleteIntersectionLocalRegularSequence
import Sheaf.RingTheory.LocalizationPrimeResidueFieldIso
import Sheaf.RingTheory.RegularSequenceConormal

/-!
# Rank of the conormal module at a complete intersection point

Source: Stacks Project, Algebra, Lemma 00SC, implication (1) implies (4)
(blueprint: lem-weil-pbc-lci-conormal-free-rank-codimension).
-/

@[expose] public section

universe u

namespace Ideal

/-- Stacks Project, Algebra, Lemma 00SC, implication (1) implies (4).
(blueprint: lem-weil-pbc-lci-conormal-free-rank-codimension)
The dimension here is the topological dimension at the point, not the dimension of its
local ring. `I.Cotangent` is `I/I²` with its canonical quotient-ring action, and
`Localization.AtPrime q.asIdeal` acts on its localization by Mathlib's fraction action
`OreLocalization.instModule`.

Proof plan, following the node's six steps:
1. Localize at `g`. The localization-prime-residue-field-iso lemma identifies the prime
   above `q` and its local ring with `S_q`. Choose a global complete intersection
   presentation `k[y₁, ..., yₘ]/J` with `t` equations and dimension `m - t`.
2. The principal-localization-open-immersion and dimension-at-point-open-subspace lemmas
   preserve dimension at `q`. Global-complete-intersection-equidimensional gives `d = m - t`.
3. Global-complete-intersection-local-regular-sequence gives a regular sequence of length
   `t` at the corresponding polynomial prime. Regular-sequence-conormal-free gives a
   free conormal module with the classes of those equations as basis.
4. Localization-module-exact identifies this conormal module with the localization of
   `J/J²`, over the local ring identified with `S_q` in step 1.
5. Conormal-module-principal-localization compares the two polynomial presentations.
   Localize its isomorphism again at the prime: if `N = (I/I²)_q`, it yields
   `N ⊕ S_q^m ≅ S_q^(t+n)`; successive module localizations identify its first term with `N`.
6. This makes `N` a finite projective module, hence flat by projective-module-flat.
   Finite-flat-local-free gives freeness. Reduction to the residue field computes the
   basis cardinality as `t + n - m = n - d`, hence also `0 ≤ d ≤ n`.
-/
theorem exists_basis_cotangent_localization_of_completeIntersection
    {k : Type u} [Field k] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) k))
    (q : PrimeSpectrum (MvPolynomial (Fin n) k ⧸ I))
    (hci : ∃ g : MvPolynomial (Fin n) k ⧸ I,
      g ∉ q.asIdeal ∧ Algebra.IsGlobalCompleteIntersection k (Localization.Away g)) :
    ∃ d : ℕ, topologicalKrullDimAt q = (d : WithBot ℕ∞) ∧ d ≤ n ∧
      Nonempty (Module.Basis (Fin (n - d)) (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl I.Cotangent)) := by
  sorry

end Ideal
