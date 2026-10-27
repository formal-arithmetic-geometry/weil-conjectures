module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # The primitive-root finite étale cover

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, VIII 5.3.6 and the proof of
Lemma 5.3.7, printed p.124 (blueprint: lem-per-cyclotomic-finite-etale-cover).

The auxiliary abbreviations specialize existing localization, quotient, and spectrum
constructions. The induced group action is specified uniquely by its two projections;
its inertia groups are equal as subsets of the original group.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The universe-lifted copy of `ℤ[1/N]` used for the primitive-root cover.
Source: ILO VIII, proof of Lemma 5.3.7, p.124
(blueprint: lem-per-cyclotomic-finite-etale-cover). -/
abbrev cyclotomicCoverBase (N : ℕ) : Type u :=
  Localization.Away (N : ULift.{u} ℤ)

/-- The actual quotient `ℤ[1/N,T]/(Φ_N(T))`, using Mathlib's `AdjoinRoot` quotient.
Source: ILO VIII, proof of Lemma 5.3.7, p.124
(blueprint: lem-per-cyclotomic-finite-etale-cover). -/
noncomputable abbrev cyclotomicCoverRing (N : ℕ) : Type u :=
  AdjoinRoot (Polynomial.cyclotomic N (cyclotomicCoverBase.{u} N))

/-- The class of the polynomial variable in the cyclotomic quotient.
Source: ILO VIII, proof of Lemma 5.3.7, p.124
(blueprint: lem-per-cyclotomic-finite-etale-cover). -/
noncomputable abbrev cyclotomicCoverRoot (N : ℕ) : cyclotomicCoverRing.{u} N :=
  AdjoinRoot.root (Polynomial.cyclotomic N (cyclotomicCoverBase.{u} N))

/-- The spectrum map induced by the coefficient inclusion into the cyclotomic quotient.
Source: ILO VIII, proof of Lemma 5.3.7, p.124
(blueprint: lem-per-cyclotomic-finite-etale-cover). -/
noncomputable abbrev cyclotomicCoverMap (N : ℕ) :
    Spec (.of (cyclotomicCoverRing.{u} N)) ⟶ Spec (.of (cyclotomicCoverBase.{u} N)) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (cyclotomicCoverBase.{u} N) (cyclotomicCoverRing.{u} N)))

/-- The primitive-root cover is finite, étale, and surjective, has the stated root and
unit differences, and remains a cover preserving geometric inertia after arbitrary base change.
Source: ILO VIII 5.3.6 and proof of Lemma 5.3.7, printed p.124
(blueprint: lem-per-cyclotomic-finite-etale-cover).

Proof plan, following the seven steps of the node:
1. By lem-per-cyclotomic-monic-positive-degree, Φ_N is monic of positive degree.
   The power basis of lem-weil-pbc-monic-quotient-free makes the quotient finite free.
   The cyclotomic product factorization gives ζ^N = 1.
2. Write T^N - 1 = Φ_N Q and differentiate. At ζ, the identity
   N ζ^(N-1) = Φ_N'(ζ) Q(ζ) makes Φ_N'(ζ) invertible. The explicit inverse identifies
   the quotient with the standard étale algebra of
   lem-weil-pbc-standard-etale-monic-derivative, proving étaleness.
3. Over each prime of the base, Φ_N remains monic of positive degree. A root in an
   algebraic closure of its residue field yields a prime of the quotient contracting
   to that prime. This proves surjectivity (def-weil-affine-spectrum).
4. For every homomorphism to an algebraically closed field, N is nonzero. Apply
   lem-per-cyclotomic-field-root-criterion and coefficient naturality to obtain a
   primitive root. These homomorphisms are precisely the geometric points of fibres.
5. For 1 ≤ a < N, primitivity shows 1 - ζ^a is nonzero in every residue field.
   Thus it belongs to no prime and is a unit, by
   lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact, clause (ii).
6. When N is invertible on W, the localization universal property and
   lem-weil-pbc-morphism-into-affine-scheme give the unique structural map s to
   Spec ℤ[1/N]. Apply lem-weil-pbc-finite-morphism-permanence,
   lem-weil-pbc-etale-scheme-base-change, and lem-weil-pbc-surjective-base-change.
7. Every automorphism of W preserves s by uniqueness. The fibre-product universal
   property therefore gives the unique induced action with trivial second projection.
   A geometric point is fixed exactly when both projections are fixed. The second
   projection is always fixed, so the stabilizers in the same group are equal.
-/
theorem cyclotomic_finite_etale_cover (N : ℕ) (hN : 1 ≤ N) :
    IsFinite (cyclotomicCoverMap.{u} N) ∧
    Etale (cyclotomicCoverMap.{u} N) ∧
    Surjective (cyclotomicCoverMap.{u} N) ∧
    cyclotomicCoverRoot.{u} N ^ N = 1 ∧
    (∀ a : ℕ, 1 ≤ a → a < N → IsUnit (1 - cyclotomicCoverRoot.{u} N ^ a)) ∧
    (∀ (Ω : Type w) [Field Ω] [IsAlgClosed Ω]
      (φ : cyclotomicCoverRing.{u} N →+* Ω),
      IsPrimitiveRoot (φ (cyclotomicCoverRoot.{u} N)) N) ∧
    (∀ (W : Scheme.{u}), IsUnit (N : Scheme.Γ.obj (op W)) →
      ∃ s : W ⟶ Spec (.of (cyclotomicCoverBase.{u} N)),
        IsFinite (pullback.fst s (cyclotomicCoverMap.{u} N)) ∧
        Etale (pullback.fst s (cyclotomicCoverMap.{u} N)) ∧
        Surjective (pullback.fst s (cyclotomicCoverMap.{u} N)) ∧
        ∀ (G : Type v) [Group G] (ρ : G →* Aut W),
          ∃! σ : G →* Aut (pullback s (cyclotomicCoverMap.{u} N)),
            (∀ g : G,
              (σ g).hom ≫ pullback.fst s (cyclotomicCoverMap.{u} N) =
                pullback.fst s (cyclotomicCoverMap.{u} N) ≫ (ρ g).hom ∧
              (σ g).hom ≫ pullback.snd s (cyclotomicCoverMap.{u} N) =
                pullback.snd s (cyclotomicCoverMap.{u} N)) ∧
            ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
              (y : Spec (.of Ω) ⟶ pullback s (cyclotomicCoverMap.{u} N)),
              {g : G | y ≫ (σ g).hom = y} =
                {g : G | (y ≫ pullback.fst s (cyclotomicCoverMap.{u} N)) ≫ (ρ g).hom =
                  y ≫ pullback.fst s (cyclotomicCoverMap.{u} N)}) := by
  sorry

end AlgebraicGeometry
