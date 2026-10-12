/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.RingTheory.Unramified.LocalStructure
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian

/-!
# Henselian local rings: étale retractions and idempotent lifting

Let `(R, 𝔪, κ)` be a local ring. We prove the following characterisations of henselian local
rings (Stacks, Lemma 04GG), following the blueprint.

* If simple roots of monic polynomials lift from `κ` to `R` (Mathlib's `HenselianLocalRing`),
  then every étale `R`-algebra `S` has, through every prime `q` over `𝔪` with trivial residue
  field extension, exactly one `R`-algebra retraction `τ : S →ₐ[R] R` with `τ⁻¹(𝔪) = q`.
* If étale `R`-algebras have such retractions, every finite `R`-algebra is a finite product of
  local rings.
* `R` is henselian (in Mathlib's sense of root lifting) if and only if idempotents of
  `B / 𝔪B` lift uniquely to `B` for every finite `R`-algebra `B`.

## Main results

- `IsLocalRing.existsUnique_algHom_comap_maximalIdeal_eq_of_forall_exists_isRoot`
- `HenselianLocalRing.existsUnique_algHom_comap_maximalIdeal_eq`
- `IsLocalRing.exists_algEquiv_pi_isLocalRing_of_forall_exists_algHom`
- `IsLocalRing.forall_existsUnique_isIdempotentElem_iff_forall_exists_isRoot`
- `HenselianLocalRing.iff_forall_existsUnique_isIdempotentElem`

## References

- Stacks Project, Lemma 10.153.3, <https://stacks.math.columbia.edu/tag/04GG>
-/

@[expose] public section

universe u v

open Polynomial IsLocalRing

namespace IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- **Finite algebras over a local ring: maximal ideals lie over the maximal ideal.** If `B` is
a finite `R`-algebra over the local ring `(R, 𝔪)`, every maximal ideal of `B` has preimage `𝔪`
in `R`.

(blueprint: `lem-weil-pbc-finite-algebra-local-radical`) -/
theorem comap_eq_maximalIdeal_of_finite {B : Type v} [CommRing B] [Algebra R B]
    [Module.Finite R B] (n : Ideal B) [n.IsMaximal] :
    n.comap (algebraMap R B) = maximalIdeal R :=
  sorry

/-- **Finite algebras over a local ring: `𝔪B` lies in the Jacobson radical.** If `B` is a
finite `R`-algebra over the local ring `(R, 𝔪)`, then `𝔪B` is contained in the Jacobson
radical of `B`.

(blueprint: `lem-weil-pbc-finite-algebra-local-radical`) -/
theorem map_maximalIdeal_le_jacobson_of_finite {B : Type v} [CommRing B] [Algebra R B]
    [Module.Finite R B] :
    (maximalIdeal R).map (algebraMap R B) ≤ Ideal.jacobson ⊥ :=
  sorry

/-- **Étale retractions over a local ring in which simple roots lift.** Let `(R, 𝔪, κ)` be a
local ring in which simple roots in `κ` of monic polynomials over `R` lift to roots in `R`, let
`S` be an étale `R`-algebra and `q` a prime of `S` lying over `𝔪` such that `κ → κ(q)` is
bijective. Then there is exactly one `R`-algebra map `τ : S →ₐ[R] R` with `τ⁻¹(𝔪) = q`.

(blueprint: `lem-weil-pbc-root-lifting-etale-retraction`) -/
theorem existsUnique_algHom_comap_maximalIdeal_eq_of_forall_exists_isRoot
    (H : ∀ f : R[X], f.Monic → ∀ a₀ : ResidueField R, aeval a₀ f = 0 →
      aeval a₀ (derivative f) ≠ 0 → ∃ a : R, f.IsRoot a ∧ residue R a = a₀)
    {S : Type v} [CommRing S] [Algebra R S] [Algebra.Etale R S] (q : Ideal S) [q.IsPrime]
    (hq : q.comap (algebraMap R S) = maximalIdeal R)
    (hκ : Function.Bijective (Ideal.ResidueField.mapₐ (maximalIdeal R) q (Algebra.ofId R S)
      hq.symm)) :
    ∃! τ : S →ₐ[R] R, (maximalIdeal R).comap τ = q :=
  sorry

/-- **Étale retractions give product decompositions of finite algebras.** Let `(R, 𝔪, κ)` be a
local ring such that for every étale `R`-algebra `R'` and every prime `𝔪'` of `R'` over `𝔪`
with `κ → κ(𝔪')` bijective there is an `R`-algebra map `τ : R' →ₐ[R] R` with `τ⁻¹(𝔪) = 𝔪'`.
Then every finite `R`-algebra is isomorphic to a finite product of local rings.

(blueprint: `lem-weil-pbc-etale-retraction-finite-product-local`) -/
theorem exists_algEquiv_pi_isLocalRing_of_forall_exists_algHom
    (H : ∀ (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra.Etale R R'] (m' : Ideal R')
      [m'.IsPrime] (hm' : m'.comap (algebraMap R R') = maximalIdeal R),
      Function.Bijective (Ideal.ResidueField.mapₐ (maximalIdeal R) m' (Algebra.ofId R R')
        hm'.symm) →
      ∃ τ : R' →ₐ[R] R, (maximalIdeal R).comap τ = m')
    (B : Type u) [CommRing B] [Algebra R B] [Module.Finite R B] :
    ∃ (r : ℕ) (B' : Fin r → Type u) (_ : ∀ i, CommRing (B' i)) (_ : ∀ i, Algebra R (B' i))
      (_ : ∀ i, IsLocalRing (B' i)), Nonempty (B ≃ₐ[R] ∀ i, B' i) :=
  sorry

/-- **Henselian local rings: idempotent lifting versus root lifting.** For a local ring
`(R, 𝔪, κ)` the following are equivalent:
(i) for every finite `R`-algebra `B`, every idempotent of `B / 𝔪B` lifts uniquely to an
idempotent of `B`;
(ii) for every monic `f ∈ R[X]` and every simple root `a₀ ∈ κ` of `f mod 𝔪` there is a root
`a ∈ R` of `f` lifting `a₀`.

(blueprint: `lem-weil-pbc-henselian-local-root-lifting`) -/
theorem forall_existsUnique_isIdempotentElem_iff_forall_exists_isRoot :
    (∀ (B : Type u) [CommRing B] [Algebra R B] [Module.Finite R B]
      (e : B ⧸ (maximalIdeal R).map (algebraMap R B)), IsIdempotentElem e →
        ∃! e' : B, IsIdempotentElem e' ∧ Ideal.Quotient.mk _ e' = e) ↔
    ∀ f : R[X], f.Monic → ∀ a₀ : ResidueField R, aeval a₀ f = 0 →
      aeval a₀ (derivative f) ≠ 0 → ∃ a : R, f.IsRoot a ∧ residue R a = a₀ :=
  sorry

end IsLocalRing

namespace HenselianLocalRing

variable {R : Type u} [CommRing R]

/-- **Étale retractions over a henselian local ring.** Let `(R, 𝔪, κ)` be a henselian local
ring, `S` an étale `R`-algebra and `q` a prime of `S` lying over `𝔪` such that `κ → κ(q)` is
bijective. Then there is exactly one `R`-algebra map `σ : S →ₐ[R] R` with `σ⁻¹(𝔪) = q`.

(blueprint: `lem-weil-pbc-henselian-etale-retraction`) -/
theorem existsUnique_algHom_comap_maximalIdeal_eq [HenselianLocalRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Algebra.Etale R S] (q : Ideal S) [q.IsPrime]
    (hq : q.comap (algebraMap R S) = maximalIdeal R)
    (hκ : Function.Bijective (Ideal.ResidueField.mapₐ (maximalIdeal R) q (Algebra.ofId R S)
      hq.symm)) :
    ∃! σ : S →ₐ[R] R, (maximalIdeal R).comap σ = q :=
  sorry

/-- **Henselian local rings lift idempotents.** A local ring `(R, 𝔪)` is henselian (in Mathlib's
sense of lifting simple roots) if and only if for every finite `R`-algebra `B` every idempotent
of `B / 𝔪B` lifts uniquely to an idempotent of `B`.

(blueprint: `lem-weil-pbc-henselian-local-root-lifting`) -/
theorem iff_forall_existsUnique_isIdempotentElem [IsLocalRing R] :
    HenselianLocalRing R ↔
      ∀ (B : Type u) [CommRing B] [Algebra R B] [Module.Finite R B]
        (e : B ⧸ (maximalIdeal R).map (algebraMap R B)), IsIdempotentElem e →
          ∃! e' : B, IsIdempotentElem e' ∧ Ideal.Quotient.mk _ e' = e :=
  sorry

end HenselianLocalRing
