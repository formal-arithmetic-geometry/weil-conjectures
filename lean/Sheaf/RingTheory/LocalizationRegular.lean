/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.RingTheory.GRing

/-!
# Localization maps are regular

Source: Stacks Project, More on Algebra, proof of Lemma 07PT and Definition 07BZ;
Algebra, Lemmas 00HT, 00DK and 00CQ, Proposition 00CP
(blueprint: lem-weil-pbc-localization-regular).
-/

@[expose] public section

universe u v

namespace IsLocalization

/-- Every localization map is regular. Its fibre at a prime disjoint from the denominators
is the residue field as an algebra over that field; otherwise its fibre is the zero ring.
Source: Stacks Project, More on Algebra, proof of Lemma 07PT and Definition 07BZ
(blueprint: lem-weil-pbc-localization-regular).

Proof:
1. The localization map is flat by `lem-weil-pbc-localization-flat` (Algebra, 00HT).
2. For a prime p, base change identifies `p.Fiber T` with a localization of `p.ResidueField`
at the image of W, by `lem-weil-pbc-localization-base-change` (Algebra, 00DK).
The tensor swap identifies this with the tensor order in the node.
3. The kernel of S to its residue field at p is p: membership in the extended maximal
ideal gives an equation u(st-a) = 0 with u and t outside p and a in p; primality forces s in p.
4. If W misses p, all its images in the residue field are nonzero, hence units; localization
at units is an algebra isomorphism. If W meets p, its image contains zero, and localization
is the zero ring. These are `lem-weil-pbc-localization-units-or-zero` (Algebra, 00CQ, 00CP).
5. Both fibres are Noetherian. Base change to any finite purely inseparable extension of
`p.ResidueField` is that extension field or the zero ring. The field is regular by
`lem-weil-pbc-field-regular-ring`; the zero ring is regular because it has no prime ideals.
Thus each fibre is geometrically regular, as in `def-weil-pbc-g-ring` (Algebra, 0382, 0381).
6. Flatness from step 1 and the fibres from step 5 give regularity by
`def-weil-pbc-g-ring` (More on Algebra, 07BZ). -/
theorem isRegular_and_fiber
    {S : Type u} {T : Type v} [CommRing S] [CommRing T] [Algebra S T]
    (W : Submonoid S) [IsLocalization W T] :
    RingHom.IsRegular (algebraMap S T) ∧
      ∀ (p : Ideal S) [p.IsPrime],
        ((∀ w : W, (w : S) ∉ p) → Nonempty (p.Fiber T ≃ₐ[p.ResidueField] p.ResidueField)) ∧
        ((∃ w : W, (w : S) ∈ p) → Subsingleton (p.Fiber T)) := by
  sorry

end IsLocalization
