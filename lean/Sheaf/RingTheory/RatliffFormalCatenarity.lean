/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q105
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.KrullDimension
public import Sheaf.RingTheory.ExcellentRing
import Mathlib.RingTheory.FiniteType
import Sheaf.RingTheory.UniversallyCatenaryDimensionFormula
import WeilConjectures.RingTheory.Flat.LocalizationPreservesFlatness
import Sheaf.RingTheory.CompleteLocalExcellent
import Sheaf.RingTheory.CompletionDimension
import Sheaf.RingTheory.FiniteAfterCompletion
import Sheaf.RingTheory.LocalCompletionQuotient
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Sheaf.RingTheory.CatenaryCompletionHyperplane
import Sheaf.RingTheory.ClosedFibrePolynomialPresentation
import Sheaf.RingTheory.ConormalTorsionAlgebraization
import Sheaf.RingTheory.FlatEquidimensionalCatenaryDescent
import Sheaf.RingTheory.OneDimensionalComponentConormal
import Sheaf.RingTheory.PolynomialClosedFibreComponents
import Sheaf.RingTheory.UniversallyCatenaryMinimalQuotients
import Sheaf.RingTheory.UniversallyCatenaryQuotient

/-!
# Ratliff's criterion for universal catenarity

Source: Stacks Project, More on Algebra, Proposition 0AW6 and Definition 0AW2,
with the proofs of Lemmas 0AW3 and 0AW5
(blueprint: lem-per-ratliff-formal-catenarity).

The formal-catenarity condition is expanded using the canonical maximal-ideal
completion and the topological dimensions of its minimal-prime quotient components.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace IsUniversallyCatenary

/-- A Noetherian local ring is universally catenary exactly when, for every minimal
prime `p`, all irreducible components of the spectrum of its completion modulo the
extension of `p` have one common finite dimension. The dimension may depend on `p`.

Source: Stacks Project, More on Algebra, Proposition 0AW6 and Definition 0AW2
(blueprint: lem-per-ratliff-formal-catenarity).

Proof, following the ten DAG steps (Tags 0AW3 and 0AW5):

1. For the forward implication assume $A$ is universally catenary. For every minimal prime
   $\mathfrak p$ of $A$, [lem-per-universal-catenarity-minimal-quotients] makes $A/\mathfrak p$
   universally catenary and [lem-weil-pbc-local-completion-quotient] identifies its completion
   with $B/\mathfrak pB$. It therefore suffices to show that every universally catenary Noetherian
   local domain has equidimensional completion. We prove this by strong induction on the least
   dimension $d$ of a completed minimal-prime quotient whenever equidimensionality fails.

2. In that domain case the completion is Noetherian and local by [lem-weil-pbc-adic-completion-
   noetherian] and [lem-weil-pbc-local-completion-local-ring]. Its dimension is $\dim A$ by [lem-
   weil-pbc-completion-dimension]. By [lem-weil-pbc-spec-irreducible-components-minimal-primes]
   its components are the $V(\mathfrak q)$ for minimal primes; their dimensions are ring quotient
   dimensions by [lem-weil-pbc-spec-topological-krull-dimension-ring]. These dimensions are finite
   by [lem-weil-pbc-noetherian-local-finite-krull-dimension]. The smallest $d$ is strictly smaller
   than $\dim A$ if they are unequal (every chain starts above some minimal prime, by [lem-weil-
   pbc-prime-contains-minimal-prime]). It is positive: a zero-dimensional minimal-prime quotient
   would make that prime the maximal ideal, hence the only prime in this local ring, making its
   spectrum equidimensional. Choose a minimal prime $\mathfrak q$ attaining $0<d<\dim A$.

3. If $d=1$, [lem-per-one-dimensional-component-conormal] supplies $J=\mathfrak q^n$ with conormal
   annihilated by a power of $\mathfrak m$. Apply [lem-per-conormal-torsion-algebraization] to the
   finite-type algebra $A$ itself: there is a finite-type $A$-algebra $D$ whose $\mathfrak m$-adic
   completion is $C=B/J$, as an $A$-algebra. Since $\sqrt J=\mathfrak q$, chains in $C$ are chains
   in $B/\mathfrak q$ and $\dim C=1$.

4. The completion reduction isomorphisms [lem-weil-pbc-adic-completion-mod-ideal] give
   $D/\mathfrak mD=C/\mathfrak mC=\kappa(\mathfrak m)$: indeed $J\subset\mathfrak
   q\subset\mathfrak mB$ and $B/\mathfrak mB=\kappa(\mathfrak m)$ by [lem-weil-pbc-local-
   completion-local-ring]. Thus $\mathfrak n=\mathfrak mD$ is maximal with that residue field.
   Modulo every $\mathfrak m^kD$, an element outside $\mathfrak n$ is a unit: lift its inverse
   modulo $\mathfrak mD$ and invert the remaining $1+u$ by the finite geometric series since
   $u^k=0$. Consequently localizing $D$ at $\mathfrak n$ leaves its $\mathfrak m$-adic completion
   unchanged. The local map $A\to D_{\mathfrak n}$ has closed fibre $\kappa(\mathfrak m)$, so
   [lem-weil-pbc-finite-after-completion] identifies this with its maximal-ideal completion. By
   [lem-weil-pbc-completion-dimension], $\dim D_{\mathfrak n}=\dim C=1$. The needed Noetherianity
   of $D$ follows from [lem-weil-pbc-finite-type-algebra-noetherian].

5. The contraction of $\mathfrak q$ to the domain $A$ is zero: the completion map is flat by [lem-
   weil-pbc-local-completion-faithfully-flat], and [lem-sc-flat-going-down] applied to the minimal
   prime $\mathfrak q$ makes its contraction minimal. Let $\mathfrak q'$ be the inverse image of
   $\mathfrak q/J$ under $D\to C$; it lies in $\mathfrak n$ and contracts to zero. Hence $A\subset
   D/\mathfrak q'$ is an inclusion of domains and the latter is finite type. Apply [lem-exc-
   dimension-formula-universally-catenary-finite-type-domain] at $\mathfrak n/\mathfrak q'$ over
   $\mathfrak m$. The residue-field transcendence degree is zero by the preceding step, so $$\dim
   (D/\mathfrak q')_{\mathfrak n}=\dim A+\operatorname{trdeg}_A(D/\mathfrak q')\ge\dim A>1.$$ But
   chains in this quotient local ring are chains in $D_{\mathfrak n}$, of dimension one. This
   contradiction proves the induction base.

6. If $d>1$, $A$ is catenary by the definition of universal catenarity [def-exc-excellent-ring],
   applied to the finite-type algebra $A$. The hyperplane reduction [lem-per-catenary-completion-
   hyperplane] gives a prime $\mathfrak p$ of $A$ and a completed minimal-prime quotient of
   $A/\mathfrak p$ of dimension $d-1$, strictly below $\dim(A/\mathfrak p)$. That quotient domain
   is universally catenary by [lem-per-universal-catenarity-quotient]. Its completion is therefore
   equidimensional by the strong induction hypothesis: if it were not, its least component
   dimension would be at most $d-1<d$. Its dimension equals $\dim(A/\mathfrak p)$ by [lem-weil-
   pbc-completion-dimension], contrary to the supplied component. This completes the forward
   implication.

7. Conversely suppose every indicated completed minimal-prime quotient is equidimensional. By
   [lem-per-universal-catenarity-minimal-quotients] it is enough to prove universal catenarity of
   each domain $A/\mathfrak p$; [lem-weil-pbc-local-completion-quotient] identifies its completion
   with $B/\mathfrak pB$. Thus rename the quotient $A$ and assume $B$ is equidimensional. The ring
   $B$ is Noetherian and local by [lem-weil-pbc-adic-completion-noetherian] and [lem-weil-pbc-
   local-completion-local-ring], and is complete by [lem-weil-pbc-adic-completion-mod-ideal]. It
   is excellent by [lem-per-complete-local-excellence], hence universally catenary by the
   definition of excellence [def-exc-excellent-ring].

8. Fix $P=A[x_1,\ldots,x_r]$ and a maximal ideal $\mathfrak n$ over $\mathfrak m$. Since
   $B/\mathfrak mB=A/\mathfrak m$ by [lem-weil-pbc-local-completion-local-ring], the quotient
   rings $B[x_1,\ldots,x_r]/\mathfrak mB[x_1,\ldots,x_r]$ and $P/\mathfrak mP$ are the same
   polynomial ring over the residue field. The inverse image $\mathfrak n'$ of $\mathfrak
   n/\mathfrak mP$ is maximal and contracts to $\mathfrak n$. By [lem-per-polynomial-closed-fibre-
   components], $Q=B[x_1,\ldots,x_r]_{\mathfrak n'}$ is catenary and equidimensional, every
   component having dimension $\dim B+r$.

9. The completion map is flat by [lem-weil-pbc-local-completion-faithfully-flat]. Its polynomial
   base change $P\to B[x_1,\ldots,x_r]$ is flat by [lem-weil-pbc-flat-module-base-change].
   Localizing the target preserves flatness by [lem-pc-affine-flat-module-localization-preserves-
   flatness], and passing to the localization of the source gives flatness over $P_{\mathfrak n}$
   by [lem-weil-pbc-flat-over-localization]. Thus $P_{\mathfrak n}\to Q$ is flat and local. Both
   rings are Noetherian (polynomial finite type by [lem-weil-pbc-finite-type-algebra-noetherian],
   and localization: an ideal is extended from its contraction, so is generated by the images of
   finitely many generators of that contraction). Apply [lem-per-flat-equidimensional-catenary-
   descent] to conclude $P_{\mathfrak n}$ is catenary.

10. Every local ring essentially of finite type over $A$ is a localization of a quotient of one of
   the rings $P_{\mathfrak n}$ just treated, by [lem-per-closed-fibre-polynomial-presentation].
   Catenarity passes to these rings directly from prime correspondence: primes of a quotient are
   primes containing its kernel, and primes of a localization are primes disjoint from the
   multiplicative set; every prime between two such primes has the same property, so the intervals
   and saturated chain lengths are unchanged. Finally, for a finite-type $A$-algebra $E$ and
   primes $\mathfrak a\subseteq\mathfrak b$, the whole interval identifies with that between
   $\mathfrak aE_{\mathfrak b}$ and $\mathfrak bE_{\mathfrak b}$ in the local ring $E_{\mathfrak
   b}$, which is essentially finite type and hence catenary. Thus $E$ is catenary. By [def-exc-
   excellent-ring] this says precisely that $A$ is universally catenary. These are the elementary
   prime-chain arguments of Tags 00NJ, 00NK and 0AUN, rather than extra black-box criteria.
-/
theorem iff_equidimensional_completed_minimal_prime_quotients
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] :
    IsUniversallyCatenary A ↔
      ∀ p : Ideal A, p ∈ minimalPrimes A →
        ∃ d : ℕ, ∀ Z ∈ irreducibleComponents
          (AlgebraicGeometry.Spec (CommRingCat.of
            (AdicCompletion (IsLocalRing.maximalIdeal A) A ⧸
              Ideal.map (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) p))),
          topologicalKrullDim Z = (d : WithBot ℕ∞) := by
  sorry

end IsUniversallyCatenary
