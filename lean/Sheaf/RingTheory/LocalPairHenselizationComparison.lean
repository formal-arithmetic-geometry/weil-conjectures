/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import WeilConjectures.RingTheory.PairHenselization
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Sheaf.RingTheory.GeneralizedHenselizationAtPrime
import WeilConjectures.RingTheory.HenselizationUniversalProperty

/-!
# Comparison of local and pair henselization

Source: Stacks Project, More on Algebra, Tag 0A03 (lemma-henselization-local-ring),
using Tag 0A02 and Algebra, Tag 04GQ
(blueprint: lem-per-local-pair-henselization-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace RingTheory

/-- Henselizing the maximal-ideal pair of a local ring gives its ordinary henselization.
Source: Stacks Project, Tag 0A03, with the pair adjunction of Tag 0A02 and the ordinary
henselization of Tag 04GQ (blueprint: lem-per-local-pair-henselization-comparison).

Here `K = c.pt.right`, `η = c.pt.hom.hom`, and `J = (maximalIdeal A).map η` are exactly
those of `lem-weil-pbc-pair-henselization`. The last clause expresses the canonical local
`A`-algebra isomorphism by its unique ring equivalence commuting with the structural maps.
The structural map of `H` is composed with `A → Aₘ` because the recorded ordinary
henselization predicate is stated over the localization at the maximal ideal.
The test rings `S` and the ordinary henselization `H` live in an arbitrary universe `v`,
independent of the universe `u` of `A` and `K`, as in the universe-polymorphic predicate
`Algebra.IsHenselizationAtPrime'`.

Proof, following the five steps of the node:
1. Apply `lem-weil-pbc-pair-henselization` to the maximal ideal. The colimit pair `(K,J)`
   is henselian and its quotient map identifies `K/J` with the nonzero field `A/𝔪`.
   Thus `J` is maximal.
2. For `z ∈ J`, the finite algebra `D = K/(1-z)` satisfies `JD = D`. The idempotent
   lifting criterion of `def-weil-pbc-henselian-terminology` gives a unique idempotent
   lifting the sole idempotent of the zero quotient. Both zero and one lift it, so
   `D = 0` and `1-z` is a unit.
3. If `x ∉ J`, lift its inverse modulo `J` to `y`. Then `1-xy ∈ J`, so step 2 makes
   `xy`, hence `x`, a unit. No member of the proper ideal `J` is a unit. Therefore
   `K` is local with maximal ideal `J`; henselianness of the pair makes it henselian
   local. Injectivity of the quotient map gives `η⁻¹(J) = 𝔪`, hence locality of `η`.
4. For henselian local `S` and local `g : A → S`, locality carries `𝔪` into the maximal
   ideal of `S`. Apply `lem-weil-pbc-henselization-universal-property` to that henselian
   pair. It gives a unique extension `h`. Elements outside `J` are units and their
   images are units, while `h(J)` lies in the maximal ideal, so `h` is local.
5. Since denominators outside `𝔪` are units, `Aₘ ≅ A`. For an ordinary henselization
   `H`, `def-weil-pbc-henselization-at-prime` and step 4 supply local maps in both
   directions. Both composites extend the structural map, so uniqueness makes them
   identities. This gives the unique local `A`-algebra equivalence `H ≃ K`.
-/
theorem local_pair_henselization_comparison (A : Type u) [CommRing A] [IsLocalRing A]
    (c : Cocone (ObjectProperty.ι (fun C : Under (CommRingCat.of A) ↦
      AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
        Function.Bijective (Ideal.quotientMap
          ((IsLocalRing.maximalIdeal A).map C.hom.hom) C.hom.hom Ideal.le_comap_map))))
    (hc : Nonempty (IsColimit c)) :
    ∃ hK : HenselianLocalRing c.pt.right,
      @IsLocalRing.maximalIdeal c.pt.right _ hK.toIsLocalRing =
          (IsLocalRing.maximalIdeal A).map c.pt.hom.hom ∧
        IsLocalHom c.pt.hom.hom ∧
        Function.Bijective (Ideal.quotientMap
          ((IsLocalRing.maximalIdeal A).map c.pt.hom.hom)
          c.pt.hom.hom Ideal.le_comap_map) ∧
        (∀ (S : Type v) [CommRing S] [HenselianLocalRing S] (g : A →+* S),
          IsLocalHom g → ∃! h : c.pt.right →+* S,
            IsLocalHom h ∧ h.comp c.pt.hom.hom = g) ∧
        (∀ (H : Type v) [CommRing H]
          [Algebra (Localization.AtPrime (IsLocalRing.maximalIdeal A)) H]
          [HenselianLocalRing H],
          Algebra.IsHenselizationAtPrime' A (IsLocalRing.maximalIdeal A) H →
            ∃! e : H ≃+* c.pt.right,
              IsLocalHom e.toRingHom ∧
                e.toRingHom.comp
                    ((algebraMap (Localization.AtPrime (IsLocalRing.maximalIdeal A)) H).comp
                      (algebraMap A (Localization.AtPrime (IsLocalRing.maximalIdeal A)))) =
                  c.pt.hom.hom) := by
  sorry

end RingTheory
