/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.RingTheory.Depth
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Sheaf.Paper.FlatLocalCriterionNonzerodivisor
import Sheaf.RingTheory.DepthQuotientNonzerodivisor
import Sheaf.RingTheory.IsRegularOfDimensionDrop
import Sheaf.RingTheory.MaximalChainLengthOfDepth
import Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence

/-!
# Miracle flatness

Source: Stacks Project, Algebra, Lemma 10.128.1 (Tag 00R4)
(blueprint: lem-weil-pbc-miracle-flatness).
-/

@[expose] public section

universe u v

namespace RingHom

/-- A local homomorphism from a regular Noetherian local ring to a Cohen–Macaulay
Noetherian local ring is flat when target dimension is source dimension plus closed
fibre dimension. The finite dimension `e` records Cohen–Macaulayness by the depth bound.
Source: Stacks Project, Algebra, Lemma 10.128.1 (Tag 00R4)
(blueprint: lem-weil-pbc-miracle-flatness).

Proof, following the node's ten steps:
1. Induct on `n = dim R`. Regular local rings have finite dimension
   (def-weil-regular-scheme). The induction assertion quantifies over all maps and targets
   satisfying the three hypotheses, not just over the given map.
2. If `n = 0`, the maximal ideal of `R` has zero generators, so `R` is a field.
   Every module over a field is flat (lem-weil-pbc-module-over-field-flat).
3. For `n > 0`, the mapped maximal ideal is proper because the map is local. The
   dimension formula gives positive target dimension and smaller closed fibre dimension.
   There are finitely many minimal primes `q_i` of `S`
   (lem-weil-pbc-noetherian-finitely-many-minimal-primes and
   lem-weil-pbc-prime-contains-minimal-prime). Their inverse images `p_i` lie in `m_R`.
4. A longest chain above `q_i` is a maximal chain of primes of `S`; Cohen–Macaulayness
   gives `dim(S/q_i) = dim S` (lem-weil-pbc-cm-local-maximal-chain-length).
5. If `p_i = m_R`, the closed fibre surjects onto `S/q_i`, contradicting its smaller
   dimension (def-weil-pbc-krull-dimension-ring). Thus every `p_i` is properly below `m_R`.
6. The cotangent dimension is `n > 0`, so `m_R` is not contained in its square
   (lem-weil-pbc-regular-local-cotangent-dimension). Prime avoidance chooses `x` in `m_R`
   outside its square and all `p_i` (lem-weil-pbc-prime-avoidance). Its image avoids all
   minimal primes of `S`.
7. Extend the class of `x` to a cotangent basis. Nakayama lifts it to `n` generators
   (lem-weil-pbc-nakayama-local-generators). These form a regular sequence; `x` is a
   nonzerodivisor and `R/xR` is regular of dimension `n - 1`
   (lem-weil-pbc-regular-local-generators-regular-sequence).
8. Avoidance of minimal primes drops the target dimension by one
   (lem-weil-pbc-noetherian-local-dim-drop-outside-minimal-primes). The dimension-drop
   criterion makes the image of `x` a nonzerodivisor
   (lem-weil-pbc-cm-local-dimension-drop-regular-sequence), and its quotient is
   Cohen–Macaulay (lem-weil-pbc-cm-local-quotient-nonzerodivisor-cm).
9. The induced map `R/xR → S/xS` is local between Noetherian local rings. Its closed
   fibre agrees with the original closed fibre, since `x` belongs to `m_R`. The two
   dimension drops preserve the dimension formula. Apply the induction hypothesis.
10. Apply the local criterion of flatness to the finite `S`-module `S` and `x`
    (lem-weil-pbc-flat-local-criterion-nonzerodivisor, def-weil-finitely-generated-module).
    Steps 7 and 8 give both nonzerodivisor conditions and step 9 gives quotient flatness.
    Hence `S` is flat over `R`, which is `φ.Flat` (def-weil-pbc-flat-ring-map).
-/
theorem flat_of_regular_of_depth_ge {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [IsRegularLocalRing R] [IsLocalRing S] [IsNoetherianRing S]
    (φ : R →+* S) [IsLocalHom φ] (e : ℕ)
    (hdim : ringKrullDim S = (e : WithBot ℕ∞))
    (hdepth : (e : ℕ∞) ≤ IsLocalRing.depth (R := S) S)
    (hdim_add : ringKrullDim S =
      ringKrullDim R + ringKrullDim (S ⧸ (IsLocalRing.maximalIdeal R).map φ)) :
    φ.Flat := by
  sorry

end RingHom
