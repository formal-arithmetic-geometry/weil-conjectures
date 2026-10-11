/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.RingTheory.Depth
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Depth formula for a flat local homomorphism

Source: Stacks Project, Algebra, Lemma 10.163.2 (Tag 0337), the ring case of
Lemma 10.163.1 (Tag 0338; EGA IV, Proposition 6.3.1)
(blueprint: lem-weil-pbc-flat-local-depth-formula).
-/

@[expose] public section

universe u v

namespace IsLocalRing

/-- A flat local homomorphism of Noetherian local rings has a Noetherian local closed
fibre, with maximal ideal the image of the target's maximal ideal, and the depth of
its target is the sum of the depths of its source and closed fibre.
Source: Stacks Project, Algebra, Tags 0337 and 0338
(blueprint: lem-weil-pbc-flat-local-depth-formula).

Proof (Tag 0338, specialized to M = R and N = S, following the node's nine steps):
1. Locality puts m_R S inside m_S. The quotient-local-structure lemma makes the
   closed fibre a nonzero local ring with maximal ideal m_S / m_R S. The
   finite-algebra-noetherian lemma makes it Noetherian. The depth-le-support-dimension
   and noetherian-local-finite-krull-dimension lemmas make all three depths finite.
2. Induct on n = depth(R) + depth(S / m_R S), uniformly over flat local maps.
3. In depth zero, nonzerodivisor-if-maximal-not-associated gives an element whose
   annihilator is the maximal ideal: otherwise a nonzerodivisor in that ideal
   would be a regular sequence of length one, contradicting the definition of depth.
4. For n = 0, choose z in R annihilated exactly by m_R and a lift y in S of an
   element of the fibre annihilated exactly by its maximal ideal. By
   annihilator-element-flat-base-change, Ann_S(phi(z)) = m_R S. Thus phi(z)y
   has annihilator m_S, and no element of m_S can start a regular sequence on S.
5. If the fibre has positive depth, lift a fibre nonzerodivisor to f in m_S.
   The flat-mod-injective lemma says f is a nonzerodivisor on S and S/fS is flat
   over R. Its closed fibre is the original fibre modulo the class of f.
6. By depth-drops-by-one and depth-over-quotient-ring, the new fibre has depth
   one less. Apply induction to R -> S/fS and the same depth lemmas to S to
   recover depth(S) = n.
7. If the fibre has depth zero and n > 0, choose a nonzerodivisor f in m_R.
   Flat base change makes phi(f) a nonzerodivisor on S. The quotient-local-structure,
   finite-algebra-noetherian and flat-module-quotient-flat lemmas make
   R/fR -> S/phi(f)S a flat local map of Noetherian local rings with the same fibre.
8. By depth-drops-by-one and depth-over-quotient-ring, the source depth drops by
   one. Induction computes the target quotient depth as n - 1; the same depth
   lemmas then compute depth(S) = n.
9. These two cases complete the induction, proving the displayed depth equality.
   The addition is in the extended natural numbers, with infinity absorbing. -/
theorem depth_eq_add_of_flat_local {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    [IsLocalRing R] [IsLocalRing S] (φ : R →+* S) [IsLocalHom φ] (hflat : φ.Flat) :
    let I : Ideal S := (maximalIdeal R).map φ
    IsNoetherianRing (S ⧸ I) ∧
      ∃ hlocal : IsLocalRing (S ⧸ I),
        letI := hlocal
        (maximalIdeal S).map (Ideal.Quotient.mk I) = maximalIdeal (S ⧸ I) ∧
          depth (R := S) S = depth (R := R) R + depth (R := S ⧸ I) (S ⧸ I) := by
  sorry

end IsLocalRing
