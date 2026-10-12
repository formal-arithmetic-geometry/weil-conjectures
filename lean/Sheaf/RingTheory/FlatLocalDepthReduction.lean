/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.RingTheory.Depth
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Sheaf.RingTheory.FlatModInjective
import Sheaf.RingTheory.AnnihilatorElementFlatBaseChange
import Sheaf.RingTheory.DepthQuotSMulTop
import Sheaf.RingTheory.DepthOverQuotientRing

/-!
# Quotients reducing the depth induction for a flat local map

Source: Stacks Project, Algebra, Tag 0338, the two positive-depth cases of the proof.
(blueprint: lem-weil-pbc-flat-local-depth-reduction).
-/

@[expose] public section

universe u v

namespace IsLocalRing

/-- A positive source-plus-fibre depth sum admits compatible proper quotients for
which both target depth and the source-plus-fibre depth sum decrease by one.
Source: Stacks Project, Algebra, Tag 0338, proof, second and third paragraphs,
specialized to the modules `M = R` and `N = S`
(blueprint: lem-weil-pbc-flat-local-depth-reduction).

Proof: Write F = S/m_R S. If depth(F) is positive, choose the first element of a
positive-length regular sequence in m_F, and lift it to f in m_S. The local
injectivity criterion (Tag 00ME, `flat_mod_injective`) applied to multiplication by
f on S shows that f is S-regular and S/fS is R-flat. Take J = 0 and K = (f), with
the induced local map R/J → S/K. Its fibre is F/(f mod m_R S). The two applications
of the regular-element depth drop (Tag 090R) to S and F, followed by change of
rings (Tag 0AUK), give the two displayed successor equalities. Here R/0 has the
same depth as R, as is seen by transporting regular sequences along R/0 ≃ R.

If depth(F) is zero, positive sum forces depth(R) positive. Choose the first term
f of a positive-length regular sequence in m_R. Flat base change of its
annihilator makes φ(f) S-regular. Take J = (f), K = (φ(f)), and the induced map
R/J → S/K. This map is flat by flat base change along R → R/J: its target is
(R/J) ⊗[R] S. Both ideals are contained in the respective maximal ideals, so the
quotients are nonzero Noetherian local rings and their induced map is local.
Its closed fibre is F, because φ(f) already belongs to m_R S. Apply Tag 090R and
Tag 0AUK to R and S to get the two equalities. In either case the quotient maps
commute with φ, as is checked on representatives. Quotient-ring identifications
preserve depth by transporting the regular sequences in the depth definition.
No depth formula for any flat local map is used in this construction. -/
theorem exists_depth_reducing_flat_local_quotients {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    [IsLocalRing R] [IsLocalRing S] (φ : R →+* S) [IsLocalHom φ] (hflat : φ.Flat)
    [IsLocalRing (S ⧸ (maximalIdeal R).map φ)]
    (hpos : 0 < depth (R := R) R +
      depth (R := S ⧸ (maximalIdeal R).map φ) (S ⧸ (maximalIdeal R).map φ)) :
    ∃ (J : Ideal R) (K : Ideal S) (hJ : J ≤ maximalIdeal R) (hK : K ≤ maximalIdeal S),
      letI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr
        (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hJ)
      letI : Nontrivial (S ⧸ K) := Ideal.Quotient.nontrivial_iff.mpr
        (ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top hK)
      letI : IsLocalRing (R ⧸ J) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
      letI : IsLocalRing (S ⧸ K) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective
      ∃ (ψ : (R ⧸ J) →+* (S ⧸ K)) (hψ : IsLocalHom ψ),
        ψ.Flat ∧
        ∃ hF : IsLocalRing ((S ⧸ K) ⧸ (maximalIdeal (R ⧸ J)).map ψ),
          letI := hF
          ψ.comp (Ideal.Quotient.mk J) = (Ideal.Quotient.mk K).comp φ ∧
          depth (R := S) S = depth (R := S ⧸ K) (S ⧸ K) + 1 ∧
          depth (R := R) R +
              depth (R := S ⧸ (maximalIdeal R).map φ) (S ⧸ (maximalIdeal R).map φ) =
            (depth (R := R ⧸ J) (R ⧸ J) +
              depth (R := (S ⧸ K) ⧸ (maximalIdeal (R ⧸ J)).map ψ)
                ((S ⧸ K) ⧸ (maximalIdeal (R ⧸ J)).map ψ)) + 1 := by
  sorry

end IsLocalRing
