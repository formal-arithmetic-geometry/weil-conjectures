/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.RingTheory.IndPrincipalZariski
public import WeilConjectures.RingTheory.ProEtale.WeaklyEtale
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
import Sheaf.RingTheory.RingKrullDimLeOfFaithfullyFlatOfIsLocalHom
import WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp
import WeilConjectures.Mathlib.RingTheory.Etale.Weakly
import Sheaf.RingTheory.WeaklyEtaleField

/-! # Dimensions of local components under a weakly etale homomorphism

Source: Silvio Greco, Two theorems on excellent rings (1976), Lemma 5.5,
printed p. 147, with the introduction's Noetherian convention and Remark 5.2
(blueprint: lem-exc-weakly-etale-local-component-dimension).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace RingHom.WeaklyEtale

/-- Every minimal component of a local weakly etale algebra over a universally catenary
local domain with finite normalization has the dimension of that domain.
Source: Greco, Two theorems on excellent rings (1976), Lemma 5.5, printed p. 147;
Remark 5.2 identifies AF with weak etaleness for Noetherian rings
(blueprint: lem-exc-weakly-etale-local-component-dimension).

Proof:
1. Fix the minimal prime P and set A = D/P and C' equal to the normalization of C.
   By lem-exc-weakly-etale-normalization-tensor, D is reduced and C' tensor D is
   the normalization D' of D, with a D-algebra splitting D' = E times F, where E is
   the normalization of A. The quotient A is a Noetherian local domain. Finite
   C-module generators of C' tensor to finite D-module generators of D'; their
   projections generate E over A, since P acts by zero. Hence E is finite over A.
2. The inclusion A into E is integral and injective, so
   lem-weil-pbc-integral-injective-dimension-equal gives dim E = dim A = d.
   The integer d is finite by lem-weil-pbc-noetherian-local-finite-krull-dimension.
   Choose a prime chain of length d in E and a maximal ideal n above its last term
   using lem-weil-pbc-proper-ideal-contained-in-maximal. The prime correspondence
   in lem-weil-pbc-localization-dimension-chains-below-prime gives dim E_n = d.
   This step uses no catenarity of A.
3. Base change gives a weakly etale C' to D' by
   lem-exc-weakly-etale-ring-base-change-composition. The projection E times F to E
   is localization at (1,0): inverting that idempotent kills the other factor.
   It is weakly etale by lem-weil-pbc-localization-ring-weakly-etale. Composition
   and localization at n give a weakly etale C' to E_n. If m is the contraction
   of n, its base change to C'_m identifies with g : C'_m to E_n via
   (a/s) tensor b mapping to h(a) h(s)^(-1) b, with inverse b mapping to 1 tensor b.
   The map g is local: a/s maps into the maximal ideal exactly when a is in m.
4. Since E is finite over A, lem-weil-pbc-finite-algebra-local-radical gives
   n intersect A equal to the maximal ideal of A. Locality of f makes m lie over
   the maximal ideal of C. By lem-weil-pbc-finite-algebra-is-integral, C to C' is
   integral, so lem-weil-pbc-integral-incomparability and
   lem-weil-pbc-proper-ideal-contained-in-maximal show m is maximal. Thus
   lem-exc-weakly-etale-normalization-dimension gives dim C'_m = dim C.
5. The local weakly etale map g is flat. By
   lem-pc-local-flat-faithful-flat-reflects-surjective it is faithfully flat, and
   lem-sc-faithfully-flat-local-dimension gives dim C'_m <= dim E_n.
6. Each fibre of g is weakly etale over a field by base change. By
   lem-weil-pbc-weak-etale-field every singly generated subalgebra is finite.
   The finite-algebra integrality theorem makes each fibre integral over that
   field, and lem-weil-pbc-integral-incomparability makes its primes incomparable.
   The inclusion-preserving correspondence in lem-weil-pbc-fibre-ring-primes-bijection
   shows that a strict prime chain in E_n contracts to a strict chain of the same
   length in C'_m. Therefore dim E_n <= dim C'_m.
7. Combine steps 2, 4, 5 and 6 to obtain dim(D/P) = dim E_n = dim C'_m = dim C.
   This includes dimension zero and is universally quantified over minimal primes.
-/
theorem ringKrullDim_quotient_minimalPrime_eq
    {C : Type u} {D : Type v} [CommRing C] [CommRing D]
    [IsNoetherianRing C] [IsLocalRing C] [IsDomain C]
    [IsNoetherianRing D] [IsLocalRing D]
    [Module.Finite C (integralClosure C (FractionRing C))]
    (f : C →+* D) [IsLocalHom f] (hf : f.WeaklyEtale)
    (hC : IsUniversallyCatenary C) (P : Ideal D) (hP : P ∈ minimalPrimes D) :
    ringKrullDim (D ⧸ P) = ringKrullDim C := by
  sorry

end RingHom.WeaklyEtale
