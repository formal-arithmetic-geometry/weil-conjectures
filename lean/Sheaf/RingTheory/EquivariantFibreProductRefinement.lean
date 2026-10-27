module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.RingHom.PurelyInseparable
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso

/-!
# Equivariant refinement of a fibre-separating product

Source: Stacks Project, Tag 0BST, `lemma-inertia-invariants-etale`, third reduction
paragraph (blueprint: lem-dl-a1-equivariant-fibre-product-refinement).
-/

@[expose] public section

universe u v w z

namespace Algebra

/-- An integral algebra with a finite group action admits an equivariant refinement of a
finite product separating a fibre, after principal localization on the base.
Source: Stacks Project, Tag 0BST, `lemma-inertia-invariants-etale`, third reduction
paragraph (blueprint: lem-dl-a1-equivariant-fibre-product-refinement).

The index set of the refinement is `Fin n`, incorporating its cardinality assertion.
The corner `(he.idem j).Corner` is exactly `e j * S_b`, with unit `e j`.
The ring equivalence and its scalar formula express the stated `B_b`-algebra equivalence,
where the scalar map into the corner is multiplication by `e j`.
The final square expresses equivariance of the canonical residue-field identifications;
comapping primes along an automorphism is the inverse of its action on primes.

Proof:
1. Pull the coordinate units back along `d` to obtain orthogonal idempotents `c_i`
   summing to one. Each fibre prime belongs to exactly one `D(c_i)`, and the hypothesis
   on each factor gives precisely `n` fibre primes.
2. For each function `a : G → Fin n`, form the product of `g(c_(a g))` over `g`.
   These are orthogonal idempotents summing to one. Left translation on functions
   permutes them, and the identity coordinate proves refinement of the original partition.
3. The clopen-idempotent correspondence (lem-weil-pbc-spec-clopen-idempotent) shows
   that these give a clopen partition. Retain the pieces meeting the fibre. Each contains
   exactly one fibre prime, giving `n` retained pieces, stable under the group action.
4. The discarded pieces form a closed set. Its image under the integral spectrum map
   is closed (lem-weil-pbc-integral-spec-closed-map) and misses `p`. The basic-open basis
   and localization homeomorphism (lem-weil-pbc-spec-localization-away-basic-open) give
   `b` outside `p` whose principal open misses that image.
5. The discarded idempotents become zero after localization, by uniqueness in the
   clopen-idempotent correspondence. The retained ones remain complete orthogonal.
   The prime correspondence in lem-weil-pbc-localization-prime-residue-field-iso
   identifies their unique fibre primes with the original ones.
6. Multiplication by the retained idempotents gives the product map. Orthogonality
   and sum one show directly that its inverse is summation and that it respects scalars.
7. Since the group fixes `b`, its action extends to fractions by acting on numerators.
   This permutes the retained idempotents and factors and commutes with prime contraction.
8. Apply lem-weil-pbc-localization-prime-residue-field-iso to the base and algebra.
   The resulting residue isomorphisms send each fraction to the same fraction after
   localization, commute with the base embeddings, and commute with the group acting
   on numerators and denominators. Thus purely inseparable extensions are preserved.
   The local-ring residue field is also the fraction field of the prime quotient.
   Relabel the retained piece containing any chosen fibre prime as the first piece. -/
theorem exists_equivariant_fibre_product_refinement
    (B : Type u) (S : Type v) [CommRing B] [CommRing S] [Algebra B S]
    (hIntegral : Algebra.IsIntegral B S)
    (G : Type z) [Group G] [Finite G] (ρ : G →* (S ≃ₐ[B] S))
    (p : PrimeSpectrum B) (n : ℕ) (hn : 0 < n)
    (D : Fin n → Type w) [∀ i, CommRing (D i)] [∀ i, Algebra B (D i)]
    (d : S ≃ₐ[B] ∀ i, D i)
    (hD : ∀ i, ∃! Q : PrimeSpectrum (D i),
      Q.asIdeal.comap (algebraMap B (D i)) = p.asIdeal) :
    ∃ (b : B), b ∉ p.asIdeal ∧
      ∃ (e : Fin n → Localization.Away (algebraMap B S b))
        (he : CompleteOrthogonalIdempotents e)
        (Φ : Localization.Away (algebraMap B S b) ≃+* ∀ j, (he.idem j).Corner),
        (∀ s j, (Φ s j).val = e j * s) ∧
        (∀ x, Φ.symm x = ∑ j, (x j).val) ∧
        (∀ a j, (Φ (Localization.awayMap (algebraMap B S) b a) j).val =
          e j * Localization.awayMap (algebraMap B S) b a) ∧
        ∃ (ρb : G →* (Localization.Away (algebraMap B S b) ≃+*
            Localization.Away (algebraMap B S b)))
          (π : G →* Equiv.Perm (Fin n)),
          (∀ g s, ρb g (algebraMap S (Localization.Away (algebraMap B S b)) s) =
            algebraMap S (Localization.Away (algebraMap B S b)) (ρ g s)) ∧
          (∀ g j, ρb g (e j) = e (π g j)) ∧
          (∀ j, ∃ i, ∀ Q : PrimeSpectrum (Localization.Away (algebraMap B S b)),
            e j ∉ Q.asIdeal →
              algebraMap S (Localization.Away (algebraMap B S b))
                (d.symm (Pi.single i 1)) ∉ Q.asIdeal) ∧
          ∃ (pb : PrimeSpectrum (Localization.Away b))
            (hpb : pb.asIdeal.comap (algebraMap B (Localization.Away b)) = p.asIdeal),
            (∀ j, ∃! Q : PrimeSpectrum (Localization.Away (algebraMap B S b)),
              Q.asIdeal.comap (Localization.awayMap (algebraMap B S) b) = pb.asIdeal ∧
                e j ∉ Q.asIdeal) ∧
            Set.BijOn
              (PrimeSpectrum.comap (algebraMap S (Localization.Away (algebraMap B S b))))
              {Q | Q.asIdeal.comap (Localization.awayMap (algebraMap B S) b) = pb.asIdeal}
              {Q | Q.asIdeal.comap (algebraMap B S) = p.asIdeal} ∧
            (∀ g (Q : PrimeSpectrum (Localization.Away (algebraMap B S b))),
              Q.asIdeal.comap (Localization.awayMap (algebraMap B S) b) = pb.asIdeal →
              (Q.asIdeal.comap (ρb g).toRingHom).comap
                  (algebraMap S (Localization.Away (algebraMap B S b))) =
                (Q.asIdeal.comap (algebraMap S (Localization.Away (algebraMap B S b)))).comap
                  (ρ g).toRingHom) ∧
            (∀ Q : PrimeSpectrum (Localization.Away (algebraMap B S b)),
              Q.asIdeal.comap (Localization.awayMap (algebraMap B S) b) = pb.asIdeal →
              ∃ σ : Equiv.Perm (Fin n), e (σ ⟨0, hn⟩) ∉ Q.asIdeal) ∧
            ∃ σB : p.asIdeal.ResidueField ≃+* pb.asIdeal.ResidueField,
              σB.toRingHom = Ideal.ResidueField.map p.asIdeal pb.asIdeal
                (algebraMap B (Localization.Away b)) hpb.symm ∧
              (∀ (Q : PrimeSpectrum (Localization.Away (algebraMap B S b)))
                (hQ : Q.asIdeal.comap (Localization.awayMap (algebraMap B S) b) = pb.asIdeal),
                ∃ (h : (Q.asIdeal.comap
                    (algebraMap S (Localization.Away (algebraMap B S b)))).comap
                      (algebraMap B S) = p.asIdeal)
                  (σQ : (Q.asIdeal.comap
                    (algebraMap S (Localization.Away (algebraMap B S b)))).ResidueField ≃+*
                      Q.asIdeal.ResidueField),
                  σQ.toRingHom = Ideal.ResidueField.map _ Q.asIdeal
                    (algebraMap S (Localization.Away (algebraMap B S b))) rfl ∧
                  σQ.toRingHom.comp (Ideal.ResidueField.map p.asIdeal _
                    (algebraMap B S) h.symm) =
                    (Ideal.ResidueField.map pb.asIdeal Q.asIdeal
                      (Localization.awayMap (algebraMap B S) b) hQ.symm).comp σB.toRingHom ∧
                  ((Ideal.ResidueField.map p.asIdeal _
                    (algebraMap B S) h.symm).IsPurelyInseparable ↔
                    (Ideal.ResidueField.map pb.asIdeal Q.asIdeal
                      (Localization.awayMap (algebraMap B S) b) hQ.symm).IsPurelyInseparable)) ∧
              (∀ (g : G) (Q : PrimeSpectrum (Localization.Away (algebraMap B S b))),
                Q.asIdeal.comap (Localization.awayMap (algebraMap B S) b) = pb.asIdeal →
                ∃ h : (Q.asIdeal.comap (ρb g).toRingHom).comap
                    (algebraMap S (Localization.Away (algebraMap B S b))) =
                  (Q.asIdeal.comap (algebraMap S (Localization.Away (algebraMap B S b)))).comap
                    (ρ g).toRingHom,
                  (Ideal.ResidueField.map (Q.asIdeal.comap (ρb g).toRingHom) Q.asIdeal
                    (ρb g).toRingHom rfl).comp
                    (Ideal.ResidueField.map _ (Q.asIdeal.comap (ρb g).toRingHom)
                      (algebraMap S (Localization.Away (algebraMap B S b))) rfl) =
                  (Ideal.ResidueField.map _ Q.asIdeal
                    (algebraMap S (Localization.Away (algebraMap B S b))) rfl).comp
                    (Ideal.ResidueField.map _
                      (Q.asIdeal.comap (algebraMap S (Localization.Away (algebraMap B S b))))
                      (ρ g).toRingHom h)) := by
  sorry

end Algebra
