/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.FieldTheory.Galois.Basic
import Sheaf.RingTheory.EtaleNormalRing
import Sheaf.RingTheory.HenselianFiniteEtaleMapBijective
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Finite Galois residue lifts over henselian normal local domains

Source: Stacks Project, `pione.tex`, Tag 0BSW (`lemma-identify-inertia`), the finite
Galois residue-extension paragraph and its omitted fraction-field calculation.
(blueprint: lem-wf-henselian-finite-galois-lift)
-/

@[expose] public section

universe u v w x y

open scoped TensorProduct

namespace HenselianLocalRing

/-- A local finite etale algebra with Galois closed fibre over a henselian normal local
 domain has the same generic and residue Galois groups, via restriction and reduction.
Source: Stacks Project, `pione.tex`, Tag 0BSW (`lemma-identify-inertia`), paragraph
beginning "Let kappa prime/kappa be a finite Galois extension".
(blueprint: lem-wf-henselian-finite-galois-lift)

Proof:
1. Normality localizes (lem-weil-pbc-localization-normal-domain), and etale maps
preserve normal rings (lem-weil-pbc-etale-over-normal-ring-normal). The localization
of the local ring B at its maximal ideal is B itself, so B is an integrally closed domain.
2. Etale algebras are flat (lem-weil-pbc-etale-algebra-flat). Finite flat modules over
local rings are free (lem-weil-pbc-finite-flat-local-free). Reducing a finite H-basis
of B gives a kappa-basis of e. Its positive size proves H -> B injective.
3. Localizing the basis at the nonzero elements of H gives a K-basis of the localized
algebra. This is a finite-dimensional domain over K, hence a field: multiplication
by a nonzero element is injective and therefore surjective. It is consequently the
fraction field E of B. The tensor map k tensor b |-> k*b is the corresponding
isomorphism, and its basis gives [E:K] = [e:kappa].
4. Finite algebras are integral (lem-weil-pbc-finite-algebra-is-integral). Conversely,
a monic polynomial over H remains monic over B. Integral closedness of B in E
therefore shows that every H-integral element of E lies in B.
5. An H-automorphism of B extends to fractions by b/c |-> tau(b)/tau(c).
A K-automorphism of E preserves the monic H-polynomials, hence preserves B by step 4.
Restriction and extension are inverse and preserve composition.
6. Henselian residue reduction is fully faithful on finite etale algebras
(lem-weil-pbc-henselian-finite-etale-map-bijective). Lift a residue automorphism and
its inverse. Their composites reduce to the identity, so faithfulness makes them
inverses. This gives the second group isomorphism with the stated reduction formula.
7. The faithful action of Aut_H(B) on E has order n = [e:kappa], by step 6 and
lem-weil-pbc-finite-galois-fixed-field. Its fixed field F contains K, and
lem-wf-finite-field-action-fixed-degree gives E/F finite Galois of degree n.
The subspace F is finite over K. Degree multiplicativity
(lem-weil-pbc-field-degree-multiplicativity) gives n = n*[F:K], hence [F:K] = 1.
Thus F = K and E/K is Galois. Combine steps 5 and 6.

The fraction fields K and E are universally quantified presentations of Frac(H)
and Frac(B); their scalar-tower instances specify the induced inclusions. These
binders occur in the conclusion, after normality and injectivity are asserted.
The H-algebra structure on e is the one induced from kappa, as specified by its
scalar tower. The given r is exactly the identification B/mB = e, retaining the
H-algebra structure. Each existential isomorphism is characterized on generators,
so these are the tensor comparison, restriction, and reduction maps of the source. -/
theorem finiteGaloisLift
    (H : Type u) [CommRing H] [HenselianLocalRing H] [IsDomain H]
    [IsIntegrallyClosed H]
    (B : Type v) [CommRing B] [IsLocalRing B] [Algebra H B]
    [Module.Finite H B] [Algebra.Etale H B]
    (e : Type w) [Field e] [Algebra (IsLocalRing.ResidueField H) e]
    [Algebra H e] [IsScalarTower H (IsLocalRing.ResidueField H) e]
    [FiniteDimensional (IsLocalRing.ResidueField H) e]
    [IsGalois (IsLocalRing.ResidueField H) e]
    (r : (B ⧸ (IsLocalRing.maximalIdeal H).map (algebraMap H B)) ≃ₐ[H] e) :
    IsDomain B ∧ IsIntegrallyClosed B ∧ Function.Injective (algebraMap H B) ∧
      ∀ (K : Type x) [Field K] [Algebra H K] [IsFractionRing H K]
        (E : Type y) [Field E] [Algebra B E] [IsFractionRing B E]
        [Algebra H E] [IsScalarTower H B E] [Algebra K E] [IsScalarTower H K E],
        FiniteDimensional K E ∧ IsGalois K E ∧
        Module.finrank K E = Module.finrank (IsLocalRing.ResidueField H) e ∧
        (∃ t : K ⊗[H] B ≃ₐ[K] E,
          ∀ (k : K) (b : B),
            t (k ⊗ₜ[H] b) = algebraMap K E k * algebraMap B E b) ∧
        (∀ a : E, IsIntegral H a ↔ ∃ b : B, algebraMap B E b = a) ∧
        ∃ (s : (E ≃ₐ[K] E) ≃* (B ≃ₐ[H] B))
          (q : (B ≃ₐ[H] B) ≃* (e ≃ₐ[IsLocalRing.ResidueField H] e)),
          (∀ (σ : E ≃ₐ[K] E) (b : B),
            algebraMap B E (s σ b) = σ (algebraMap B E b)) ∧
          ∀ (τ : B ≃ₐ[H] B) (b : B),
            q τ (r (Ideal.Quotient.mk _ b)) = r (Ideal.Quotient.mk _ (τ b)) := by
  sorry

end HenselianLocalRing
