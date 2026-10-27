module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Noetherian.Defs

import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.AlgebraicGeometry.SpecFieldPointResidueField
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.PropertyC

/-!
# Dimension bound for a finite type Laurent polynomial subalgebra

Source: Stacks Project, Morphisms, Tags 0BAG (`lemma-alteration-dimension-general`)
and 0BAE (`lemma-dimension-formula-general`), with reduction along minimal primes
(blueprint: lem-per-laurent-subalgebra-dimension-bound).
-/

@[expose] public section

universe u

namespace LaurentPolynomial

/-- A finite type subalgebra of a one-variable Laurent polynomial algebra over a nonzero
Noetherian ring of finite dimension `d` has dimension at most `d + 1`.
Source: Stacks Project, Morphisms, Tags 0BAG and 0BAE
(blueprint: lem-per-laurent-subalgebra-dimension-bound).

Proof plan:
1. By lem-weil-pbc-noetherian-finitely-many-minimal-primes, enumerate the finitely many
   minimal primes p_i of R. They form a nonempty family, since otherwise
   lem-per-nilradical-minimal-prime-intersection would make 1 nilpotent in R. Set
   D_i = R/p_i and F_i = Frac(D_i), using lem-weil-pbc-prime-residue-field-algebra.
   Reducing Laurent coefficients defines B -> D_i[T,T^-1] -> F_i(T). The last map is
   injective: multiply a Laurent sum by a large power of T and use polynomial coefficient
   injectivity. Its kernel K_i in B is prime and contracts to p_i in R.
2. An element in every K_i has nilpotent coefficients by
   lem-per-nilradical-minimal-prime-intersection. For its finitely many nonzero
   coefficients r_j choose positive e_j with r_j^e_j = 0. Its power
   1 + sum_j (e_j - 1) vanishes, because each monomial repeats some r_j at least e_j times.
   For the zero Laurent polynomial use exponent 1. Thus the intersection of the K_i lies
   in every prime q of B. If no K_i were contained in q, choose b_i in K_i outside q;
   their product lies in q, contradicting primality. Every minimal prime of B is some K_i.
3. For q = K_i, the injection B/q -> F_i(T) extends to Frac(B/q) by a/b -> rho_i(a)/rho_i(b).
   Nonzero denominators and cross multiplication verify well-definedness and injectivity.
   Constants give D_i -> B/q, hence F_i -> Frac(B/q), with the usual composite into F_i(T).
   These are the residue-field embeddings, not maps to a fibre ring.
4. By def-weil-rational-function-field, every z in F_i(T) is P(T)/Q(T), Q nonzero.
   It satisfies the nonzero polynomial Q(T)Z - P(T) over F_i[T]. Apply
   lem-sfb-algebraic-adjoin-transcendence-bound to the singleton {T} to get transcendence
   degree at most one. Injectivity preserves algebraic independence of subsets of
   Frac(B/q); def-kun-transcendence-degree gives the same bound for that field over F_i.
5. By def-weil-affine-spectrum, form Spec B -> Spec R. Finite type and
   lem-weil-pbc-lft-pointwise-criterion make this locally of finite type; pqf-def-locnoeth
   makes Spec R locally Noetherian. By lem-weil-pbc-spec-irreducible-components-minimal-primes
   and lem-weil-pbc-spec-irreducible-closed-subsets-primes, the component generic points
   correspond to the minimal primes q of B. The identifications of
   lem-weil-pbc-spec-field-point-residue-field and the compatibility of
   lem-weil-pbc-spec-map-residue-field-naturality identify the generic residue-field maps
   with the fraction maps in step 3. Step 4 therefore bounds every such degree by one.
6. Apply lem-sfb-generic-residue-transcendence-dimension-bound with n = 1 to obtain
   dim(Spec B) <= dim(Spec R) + 1. By def-weil-pbc-krull-dimension-ring and the hypothesis
   dim R = d, this is dim B <= d + 1. -/
theorem ringKrullDim_subalgebra_le
    (R : Type u) [CommRing R] [Nontrivial R] [IsNoetherianRing R]
    (d : ℕ) (hd : ringKrullDim R = (d : WithBot ℕ∞))
    (B : Subalgebra R (LaurentPolynomial R))
    (hB : (algebraMap R B).FiniteType) :
    ringKrullDim B ≤ ((d + 1 : ℕ) : WithBot ℕ∞) := by
  sorry

end LaurentPolynomial
