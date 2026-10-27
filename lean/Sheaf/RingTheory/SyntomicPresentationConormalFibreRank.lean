/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Extension.Generators
public import WeilConjectures.RingTheory.CompleteIntersectionOverField
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
import WeilConjectures.RingTheory.SyntomicAtPrimeRelativeGlobalCompleteIntersection
import WeilConjectures.RingTheory.ConormalModulePrincipalLocalization
import WeilConjectures.RingTheory.RelativeGlobalCompleteIntersectionConormalFree
import WeilConjectures.RingTheory.FiniteProjectivePrimeLocalFree
import Sheaf.RingTheory.FiniteProjectiveOfStandardCover
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import WeilConjectures.RingTheory.LciConormalFreeRankCodimension
import Mathlib.Algebra.Module.Projective

/-!
# Conormal modules of syntomic polynomial presentations

Source: Stacks Project, Algebra, Tags 07BT and 00SC, (1) implies (4), with
Tags 00HL and 00DF for the fibre comparison
(blueprint: lem-sfb-syntomic-presentation-conormal-fibre-rank).
-/

@[expose] public section

universe u v

set_option autoImplicit false

open scoped TensorProduct

namespace Algebra

/-- A syntomic polynomial presentation has finite projective conormal, with canonical
residue-field comparison and the expected local fibre rank.
Source: Stacks Project, Algebra, Tags 07BT (g = 1), 00SC (1) implies (4), 00HL and 00DF
(blueprint: lem-sfb-syntomic-presentation-conormal-fibre-rank).

The first clause exhibits a splitting through a finite free S-module. For the comparison,
we use the canonical identification F tensor_S N = k tensor_R N (and tensor symmetry),
where k is the residue field and F = k tensor_R S. The map e is characterized on every
conormal class by coefficient reduction; its k-linearity and this formula also give
F-linearity for the transported F-action. The target is the conormal of the polynomial
presentation supplied by Generators.baseChange, not of the tensor polynomial ring.
The last dimension is topologicalKrullDimAt, not the dimension of the local ring.

Proof:
1. At a prime q of S, flat-local-ring-maps gives a flat local map R_p to S_q.
The local complete intersection fibre supplies a global complete intersection
neighbourhood. Apply syntomic-at-prime-relative-global-complete-intersection with g = 1.
2. Conormal-module-principal-localization compares N localized at that chart with
its relative complete intersection conormal, up to finite free summands.
Relative-global-complete-intersection-conormal-free makes the latter finite free,
so the localized N is finite projective.
3. Finite-projective-prime-local-free refines these neighbourhoods to ones where N is
finite free. Writing the second localizing element as a/g^r replaces the iterated
localization by localization at ga, with a outside q.
4. Spec-basic-opens-unit-ideal-quasi-compact gives a finite standard cover.
Affine-standard-cover-finite-projective makes N finite projective. A finite generating
surjection from S^r splits by projectivity, giving i and r below. This includes S = 0.
5. Tensor 0 to J to R[x] to S to 0 with k. Flat-quotient-tensor-injective applies
because S is R-flat; it does not require R-flatness of k. Polynomial-scalar-extension
identifies k tensor_R J with the kernel of the coefficient-reduced presentation.
6. Tensor right exactness applied to J^2 to J to N to 0 identifies its cokernel
with Jbar/Jbar^2: the image of k tensor_R J^2 is exactly Jbar^2, by expanding products.
The resulting comparison sends a tensor [j] to a times [jbar], the displayed formula.
The associativity comparison sends [j] tensor (s tensor a) to a tensor s[j].
7. At every prime q of F, the fibre hypothesis gives a global complete intersection
neighbourhood. Lci-conormal-free-rank-codimension gives a natural dimension d at most n
and the basis of size n-d. If F = 0 there are no such primes, and the comparison is
still the zero-module isomorphism. -/
theorem syntomic_presentation_conormal_fibre_rank
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] [FinitePresentation R S]
    (hci : ∀ p : PrimeSpectrum R,
      IsLocalCompleteIntersection p.asIdeal.ResidueField (p.asIdeal.Fiber S))
    (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] S) (hα : Function.Surjective α)
    (hJ : (RingHom.ker α.toRingHom).FG) :
    (∃ (m : ℕ)
      (i : (Extension.ofSurjective α hα).Cotangent →ₗ[S] (Fin m → S))
      (r : (Fin m → S) →ₗ[S] (Extension.ofSurjective α hα).Cotangent),
      r.comp i = LinearMap.id) ∧
    ∀ p : PrimeSpectrum R,
      (∃ e : p.asIdeal.ResidueField ⊗[R] (Extension.ofSurjective α hα).Cotangent
          ≃ₗ[p.asIdeal.ResidueField]
            ((Generators.ofAlgHom α hα).baseChange p.asIdeal.ResidueField).toExtension.Cotangent,
        ∀ (a : p.asIdeal.ResidueField) (j : (Extension.ofSurjective α hα).ker)
          (j' : ((Generators.ofAlgHom α hα).baseChange
            p.asIdeal.ResidueField).toExtension.ker),
          j'.val = MvPolynomial.map (algebraMap R p.asIdeal.ResidueField) j.val →
            e (a ⊗ₜ[R] Extension.Cotangent.mk j) = a • Extension.Cotangent.mk j') ∧
      ∀ q : PrimeSpectrum (p.asIdeal.Fiber S),
        ∃ d : ℕ, topologicalKrullDimAt q = (d : WithBot ℕ∞) ∧ d ≤ n ∧
          Nonempty (Module.Basis (Fin (n - d)) (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl
              ((Generators.ofAlgHom α hα).baseChange
                p.asIdeal.ResidueField).toExtension.Cotangent)) := by
  sorry

end Algebra
