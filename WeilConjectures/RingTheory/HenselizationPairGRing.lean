/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import WeilConjectures.RingTheory.PairHenselization
import WeilConjectures.RingTheory.HenselizationPairGRingCore

/-!
# G-rings and henselizations of pairs

If `A` is a G-ring, then the henselization of any pair `(A, I)` is a G-ring
(`RingTheory.isGRing_of_pair_henselization`).

## Implementation details

The henselization is Noetherian and flat over `A` with the same `I`-adic completion. At each
maximal ideal, its local ring and the corresponding local ring of `A` have isomorphic completions,
and the fibres of the henselization are finite products of separable algebraic extensions of the
residue fields. Hence the formal fibres of the henselization are direct factors of base changes of
formal fibres of `A` along separable algebraic extensions, which stay geometrically regular. The
maximal-ideal criterion for G-rings concludes.

## References

* [Stacks, Tag 0AH3]
* [Stacks, Tag 0A02]
* [Stacks, Tag 0AGV]
* [Stacks, Tag 0AGX]
* [Stacks, Tag 0AH1]
* [Stacks, Tag 07QH]
* [Stacks, Tag 07PT]
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace RingTheory

/-- If `A` is a G-ring, then the ring in a henselization of the pair `(A, I)` is a
G-ring. Here a henselization is represented by its colimit cocone, together with
the colimit, henselian-pair, and quotient-isomorphism properties of
`pair_henselization`.
-/
theorem isGRing_of_pair_henselization
    (A : Type u) [CommRing A] (I : Ideal A)
    (c : Cocone (ObjectProperty.ι
      (fun C : Under (CommRingCat.of A) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
          Function.Bijective (Ideal.quotientMap (I.map C.hom.hom) C.hom.hom
            (Ideal.le_comap_map)))))
    (hc : Nonempty (IsColimit c) ∧
      HenselianRing c.pt.right (I.map c.pt.hom.hom) ∧
      Function.Bijective (Ideal.quotientMap (I.map c.pt.hom.hom) c.pt.hom.hom
        (Ideal.le_comap_map)))
    (hA : IsGRing A) : IsGRing c.pt.right := by
  obtain ⟨hn, hm⟩ := henselization_pair_noetherian_and_maximal_regular A I c hc hA
  let _ : IsNoetherianRing c.pt.right := hn
  exact (isGRing_iff_maximalIdeal c.pt.right).2 hm

end RingTheory
