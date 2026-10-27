/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import Sheaf.RingTheory.GeneralizedHenselizationAtPrime
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.RingTheory.PairHenselization
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.AlgebraicGeometry.ResidueField
import Sheaf.RingTheory.PrimePairColimitIndEtaleModel
import Sheaf.RingTheory.InitialHenselianColimitComparison
import WeilConjectures.RingTheory.MapIntoHenselianColimit
import Sheaf.TraceFormula.HenselizationQuotientAtPrime

/-!
# Pointed étale invariance of ordinary henselizations

Source: Stacks Project, Algebra, Tags 08HQ, 04GQ, 05WQ; More on Algebra, Tags 0A02,
0A03 (blueprint: lem-trf-pointed-etale-henselization-isomorphism).

The declarations separately record existence, the pair-colimit description, and the
comparison for arbitrary choices, including its inverse and every closed quotient.
-/

@[expose] public section

set_option autoImplicit false

universe u v w x

open CategoryTheory CategoryTheory.Limits

namespace Algebra

/-- The specified structural map from the original ring to its chosen henselization.
Source: Stacks Project, Algebra, Tag 04GQ
(blueprint: lem-trf-pointed-etale-henselization-isomorphism). -/
def ordinaryHenselizationBaseMap (A : Type u) [CommRing A] (p : Ideal A) [p.IsPrime]
    (H : Type v) [CommRing H] [Algebra (Localization.AtPrime p) H] : A →+* H :=
  (algebraMap (Localization.AtPrime p) H).comp (algebraMap A (Localization.AtPrime p))

/-- Existence of an ordinary henselization, used for each of the two local rings.
Source: Stacks Project, More on Algebra, Tags 0A02 and 0A03; Algebra, Tag 04GQ
(blueprint: lem-trf-pointed-etale-henselization-isomorphism).

Proof (node step 1). Apply lem-weil-pbc-pair-henselization to the maximal ideal of
`Aₚ`. By lem-trf-prime-pair-colimit-ind-etale-model its pair-colimit is henselian
local, with local structural map and unchanged residue field. Apply
lem-weil-pbc-map-into-henselian-colimit to a test henselian local ring and the induced
residue map. Its uniqueness is uniqueness among local maps, since such maps have the
same maximal-ideal preimage and structural residue map. This gives precisely the
universal property in def-weil-pbc-henselization-at-prime. -/
theorem exists_ordinaryHenselization_atPrime (A : Type u) [CommRing A]
    (p : Ideal A) [p.IsPrime] :
    ∃ (H : Type u) (_ : CommRing H) (_ : Algebra (Localization.AtPrime p) H)
      (_ : HenselianLocalRing H), IsHenselizationAtPrime' A p H := by
  sorry

/-- Any pair-colimit at the maximal ideal of `Aₚ` is an ordinary henselization, with
its specified structure map, maximal ideal, and structural residue isomorphism.
Source: Stacks Project, More on Algebra, Tags 0A02 and 0A03
(blueprint: lem-trf-pointed-etale-henselization-isomorphism).

Proof (node step 1). Apply lem-trf-prime-pair-colimit-ind-etale-model, transporting
between the full neighborhood category and a small skeleton, to get the henselian
local structure, maximal-ideal equality, local base map and structural residue
isomorphism. For a local map into a henselian local ring, apply
lem-weil-pbc-map-into-henselian-colimit to this étale colimit and its unique compatible
residue map. Every local extension induces that same residue map, proving uniqueness.
The same argument applies separately to `Aₚ` and `C_q`. -/
theorem pairColimit_isOrdinaryHenselization (A : Type u) [CommRing A]
    (p : Ideal A) [p.IsPrime]
    (c : Cocone (ObjectProperty.ι
      (fun B : Under (CommRingCat.of (Localization.AtPrime p)) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map B.hom) ∧
          Function.Bijective (Ideal.quotientMap
            ((IsLocalRing.maximalIdeal (Localization.AtPrime p)).map B.hom.hom)
            B.hom.hom Ideal.le_comap_map))))
    (_hc : IsColimit c) :
    ∃ hH : HenselianLocalRing c.pt.right,
      @IsLocalRing.maximalIdeal c.pt.right _ hH.toIsLocalRing =
        (IsLocalRing.maximalIdeal (Localization.AtPrime p)).map c.pt.hom.hom ∧
      Function.Bijective (Ideal.quotientMap
        ((IsLocalRing.maximalIdeal (Localization.AtPrime p)).map c.pt.hom.hom)
        c.pt.hom.hom Ideal.le_comap_map) ∧
      @IsHenselizationAtPrime' A _ p c.pt.right _ _ c.pt.hom.hom.toAlgebra hH := by
  sorry

/-- A pointed étale map with unchanged residue field identifies arbitrary ordinary
henselizations, their inverse pointed maps, and all the specified closed quotients.

Source: Stacks Project, Algebra, Tags 08HQ, 04GQ, 05WQ; More on Algebra, Tag 0A03
(blueprint: lem-trf-pointed-etale-henselization-isomorphism).

Proof (the five steps of the node).
1. Existence and the pair-colimit assertions are recorded above. Compare any initial
   choices with these colimits by lem-trf-initial-henselian-colimit-comparison. The
   comparison preserves structural maps, maximal ideals and structural residue maps.
2. The localization map `r = Localization.localRingHom p q φ hp` is local: its
   denominators avoid `q` and its maximal-ideal preimage is `p Aₚ`. Initiality gives
   the unique local extension `α : H → K`. Tag 08HQ, in
   lem-weil-pbc-map-into-henselian-colimit, gives the unique pointed `A`-map `f : C → H`
   for the inverse residue-field isomorphism. Elements outside `q` map to units, so
   `f` extends to a local map `C_q → H`, then by initiality to `β : K → H`.
3. The composite `βα` extends the structure map of `H`, hence is the identity.
   The two maps `C → K` given by `αf` and the structure map have the same residue map:
   the residue of `α` is the given residue-field isomorphism. Tag 08HQ uniqueness
   identifies them. On fractions `αβ` therefore fixes `C_q`; initiality makes it the
   identity on `K`. These maps give `e` and the stated inverse characterization.
4. For `a ∈ I`, the structural compatibility gives `α(i(a)) = j(φ(a))`.
   Surjectivity identifies the ideals generated by these elements. The maps induced
   by `α` and `β` on quotients are inverse. Compatibility over `A/I` follows from
   `αi = jr`, and compatibility over `C/IC` follows from `αf` being the structure map.
5. Apply lem-trf-henselization-quotient-at-prime (Tag 05WQ) to the extended ideals
   inside the maximal ideals of `Aₚ` and `C_q`. Identify the local quotients with
   `(A/I)_(p/I)` and `(C/IC)_(q/IC)` by `[a/s] ↦ [a]/[s]` and its inverse. These
   identifications are local and preserve structure maps, so they preserve the
   initial local-map universal properties asserted below. -/
theorem pointedEtale_henselization_isomorphism
    (A : Type u) (C : Type v) [CommRing A] [CommRing C]
    (φ : A →+* C) (_hφ : φ.Etale)
    (p : Ideal A) [p.IsPrime] (q : Ideal C) [q.IsPrime]
    (hp : p = q.comap φ)
    (hres : Function.Bijective (Ideal.ResidueField.map p q φ hp))
    (H : Type w) (K : Type x) [CommRing H] [CommRing K]
    [Algebra (Localization.AtPrime p) H] [Algebra (Localization.AtPrime q) K]
    [HenselianLocalRing H] [HenselianLocalRing K]
    (_hH : IsHenselizationAtPrime' A p H) (_hK : IsHenselizationAtPrime' C q K) :
    (IsLocalRing.maximalIdeal H =
      (IsLocalRing.maximalIdeal (Localization.AtPrime p)).map
        (algebraMap (Localization.AtPrime p) H)) ∧
    (IsLocalRing.maximalIdeal K =
      (IsLocalRing.maximalIdeal (Localization.AtPrime q)).map
        (algebraMap (Localization.AtPrime q) K)) ∧
    ∃ (eH : p.ResidueField ≃+* IsLocalRing.ResidueField H)
      (eK : q.ResidueField ≃+* IsLocalRing.ResidueField K),
      eH.toRingHom.comp (IsLocalRing.residue (Localization.AtPrime p)) =
        (IsLocalRing.residue H).comp (algebraMap (Localization.AtPrime p) H) ∧
      eK.toRingHom.comp (IsLocalRing.residue (Localization.AtPrime q)) =
        (IsLocalRing.residue K).comp (algebraMap (Localization.AtPrime q) K) ∧
      ∃ e : H ≃+* K,
        IsLocalHom e.toRingHom ∧
        e.toRingHom.comp (algebraMap (Localization.AtPrime p) H) =
          (algebraMap (Localization.AtPrime q) K).comp
            (Localization.localRingHom p q φ hp) ∧
        (∀ α : H →+* K, IsLocalHom α →
          α.comp (algebraMap (Localization.AtPrime p) H) =
            (algebraMap (Localization.AtPrime q) K).comp
              (Localization.localRingHom p q φ hp) → α = e.toRingHom) ∧
        ∃ f : C →+* H,
          f.comp φ = ordinaryHenselizationBaseMap A p H ∧
          q = (IsLocalRing.maximalIdeal H).comap f ∧
          (IsLocalRing.residue H).comp f = eH.toRingHom.comp
            ((RingEquiv.ofBijective (Ideal.ResidueField.map p q φ hp) hres).symm.toRingHom.comp
              (algebraMap C q.ResidueField)) ∧
          (∀ f' : C →+* H,
            f'.comp φ = ordinaryHenselizationBaseMap A p H →
            q = (IsLocalRing.maximalIdeal H).comap f' →
            (IsLocalRing.residue H).comp f' = eH.toRingHom.comp
              ((RingEquiv.ofBijective (Ideal.ResidueField.map p q φ hp) hres).symm.toRingHom.comp
                (algebraMap C q.ResidueField)) → f' = f) ∧
          e.symm.toRingHom.comp (ordinaryHenselizationBaseMap C q K) = f ∧
          ∀ (I : Ideal A), I ≤ p →
            ∃ (JH : Ideal H) (JK : Ideal K),
              JH = I.map (ordinaryHenselizationBaseMap A p H) ∧
              JK = (I.map φ).map (ordinaryHenselizationBaseMap C q K) ∧
              JH.map e.toRingHom = JK ∧
              ∃ (E : (H ⧸ JH) ≃+* (K ⧸ JK))
                (a : (A ⧸ I) →+* (H ⧸ JH))
                (b : (C ⧸ I.map φ) →+* (K ⧸ JK))
                (c : (C ⧸ I.map φ) →+* (H ⧸ JH)),
                E.toRingHom.comp (Ideal.Quotient.mk JH) =
                  (Ideal.Quotient.mk JK).comp e.toRingHom ∧
                a.comp (Ideal.Quotient.mk I) =
                  (Ideal.Quotient.mk JH).comp (ordinaryHenselizationBaseMap A p H) ∧
                b.comp (Ideal.Quotient.mk (I.map φ)) =
                  (Ideal.Quotient.mk JK).comp (ordinaryHenselizationBaseMap C q K) ∧
                c.comp (Ideal.Quotient.mk (I.map φ)) =
                  (Ideal.Quotient.mk JH).comp f ∧
                E.toRingHom.comp a =
                  b.comp (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map) ∧
                E.toRingHom.comp c = b ∧
                ∃ (hpI : (p.map (Ideal.Quotient.mk I)).IsPrime)
                  (hqI : (q.map (Ideal.Quotient.mk (I.map φ))).IsPrime)
                  (aH : Algebra (Localization.AtPrime (p.map (Ideal.Quotient.mk I))) (H ⧸ JH))
                  (aK : Algebra (Localization.AtPrime
                    (q.map (Ideal.Quotient.mk (I.map φ)))) (K ⧸ JK))
                  (hQH : HenselianLocalRing (H ⧸ JH))
                  (hQK : HenselianLocalRing (K ⧸ JK)),
                  @IsHenselizationAtPrime' (A ⧸ I) _ (p.map (Ideal.Quotient.mk I))
                    (H ⧸ JH) hpI _ aH hQH ∧
                  @IsHenselizationAtPrime' (C ⧸ I.map φ) _
                    (q.map (Ideal.Quotient.mk (I.map φ))) (K ⧸ JK) hqI _ aK hQK ∧
                  (algebraMap (Localization.AtPrime (p.map (Ideal.Quotient.mk I)))
                    (H ⧸ JH)).comp
                    (algebraMap (A ⧸ I)
                      (Localization.AtPrime (p.map (Ideal.Quotient.mk I)))) = a ∧
                  (algebraMap (Localization.AtPrime
                    (q.map (Ideal.Quotient.mk (I.map φ)))) (K ⧸ JK)).comp
                    (algebraMap (C ⧸ I.map φ)
                      (Localization.AtPrime (q.map (Ideal.Quotient.mk (I.map φ))))) = b := by
  sorry

end Algebra
