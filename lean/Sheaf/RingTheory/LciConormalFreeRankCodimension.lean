/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import WeilConjectures.RingTheory.CompleteIntersectionOverField
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
import all WeilConjectures.RingTheory.SmoothAtPrimeDifferentialsDimension
import Sheaf.AlgebraicGeometry.GlobalCompleteIntersectionEquidimensional
import Sheaf.RingTheory.CompleteIntersectionPresentationStableConormal
import Mathlib.RingTheory.LocalRing.Module

/-!
# Rank of the conormal module at a complete intersection point

Source: Stacks Project, Algebra, Lemma 00SC, implication (1) implies (4)
(blueprint: lem-weil-pbc-lci-conormal-free-rank-codimension).
-/

@[expose] public section

universe u

namespace Ideal

private theorem basis_of_stably_free {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (a b : ℕ)
    (e : (M × (Fin a → R)) ≃ₗ[R] (Fin b → R)) :
    a ≤ b ∧ Nonempty (Module.Basis (Fin (b - a)) R M) := by
  let i : M →ₗ[R] (Fin b → R) := e.toLinearMap.comp (LinearMap.inl R M (Fin a → R))
  let s : (Fin b → R) →ₗ[R] M :=
    (LinearMap.fst R M (Fin a → R)).comp e.symm.toLinearMap
  have hs : s.comp i = LinearMap.id := by
    ext x
    simp [s, i]
  let : Module.Projective R M := Module.Projective.of_split i s hs
  let : Module.Finite R M := Module.Finite.of_surjective s (by
    intro x
    exact ⟨i x, LinearMap.congr_fun hs x⟩)
  let : Module.Free R M := Module.free_of_flat_of_isLocalRing
  have hr : Module.finrank R M + a = b := by
    simpa only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin] using e.finrank_eq
  refine ⟨by omega, ⟨Module.finBasisOfFinrankEq R M (by omega)⟩⟩

private theorem principal_ci_presentation_dimension {k : Type u} [Field k] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) k))
    (q : PrimeSpectrum (MvPolynomial (Fin n) k ⧸ I))
    (hci : ∃ g : MvPolynomial (Fin n) k ⧸ I,
      g ∉ q.asIdeal ∧ Algebra.IsGlobalCompleteIntersection k (Localization.Away g)) :
    ∃ (g : MvPolynomial (Fin n) k ⧸ I) (m t : ℕ)
      (f : Fin t → MvPolynomial (Fin m) k),
      g ∉ q.asIdeal ∧ t ≤ m ∧
      Nonempty ((MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range f)) ≃ₐ[k]
        Localization.Away g) ∧
      topologicalKrullDim (PrimeSpectrum (Localization.Away g)) =
        ((m - t : ℕ) : WithBot ℕ∞) ∧
      topologicalKrullDimAt q = ((m - t : ℕ) : WithBot ℕ∞) := by
  obtain ⟨g, hg, hG⟩ := hci
  have hqopen : q ∈ PrimeSpectrum.basicOpen g :=
    (PrimeSpectrum.mem_basicOpen g q).2 hg
  have hqopen' : q ∈ (↑(PrimeSpectrum.basicOpen g) : Set _) := hqopen
  rw [← PrimeSpectrum.localization_away_comap_range
    (S := Localization.Away g) (r := g)] at hqopen'
  obtain ⟨p, hp⟩ := hqopen'
  have hpq : PrimeSpectrum.comap (algebraMap _ (Localization.Away g)) p = q := hp
  let _ : Nontrivial (Localization.Away g) :=
    (PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨p⟩)
  rcases hG with hzero | ⟨m, t, f, htm, ⟨e⟩, hdim⟩
  · exact (zero_ne_one (hzero.elim 0 1)).elim
  let H := PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv
  let p' : PrimeSpectrum (MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range f)) := H.symm p
  have hp'dim : topologicalKrullDimAt p' = ((m - t : ℕ) : WithBot ℕ∞) := by
    have hlocal :=
      AlgebraicGeometry.topologicalKrullDimAt_spec_quotient_mvPolynomial_of_eq
        k m t f e.toEquiv.nontrivial
        ⟨htm, (H.isHomeomorph.topologicalKrullDim_eq H).trans hdim⟩ p'
    exact hlocal
  have hpd : topologicalKrullDimAt p = topologicalKrullDimAt p' := by
    simpa [p'] using (Algebra.dimAt_openEmbedding H.isOpenEmbedding p').symm
  have hqd : topologicalKrullDimAt q = topologicalKrullDimAt p := by
    rw [← hpq]
    exact (Algebra.dimAt_openEmbedding
      (PrimeSpectrum.localization_away_isOpenEmbedding (Localization.Away g) g) p).symm
  refine ⟨g, m, t, f, hg, htm, ⟨e⟩, hdim, ?_⟩
  exact hqd.trans (hpd.trans hp'dim)

/-- Stacks Project, Algebra, Lemma 00SC, implication (1) implies (4).
(blueprint: lem-weil-pbc-lci-conormal-free-rank-codimension)
The dimension here is the topological dimension at the point, not the dimension of its
local ring. `I.Cotangent` is `I/I²` with its canonical quotient-ring action, and
`Localization.AtPrime q.asIdeal` acts on its localization by Mathlib's fraction action
`OreLocalization.instModule`.

Proof plan, following the node's six steps:
1. Localize at `g`. The localization-prime-residue-field-iso lemma identifies the prime
   above `q` and its local ring with `S_q`. Choose a global complete intersection
   presentation `k[y₁, ..., yₘ]/J` with `t` equations and dimension `m - t`.
2. The principal-localization-open-immersion and dimension-at-point-open-subspace lemmas
   preserve dimension at `q`. Global-complete-intersection-equidimensional gives `d = m - t`.
3. Global-complete-intersection-local-regular-sequence gives a regular sequence of length
   `t` at the corresponding polynomial prime. Regular-sequence-conormal-free gives a
   free conormal module with the classes of those equations as basis.
4. Localization-module-exact identifies this conormal module with the localization of
   `J/J²`, over the local ring identified with `S_q` in step 1.
5. Conormal-module-principal-localization compares the two polynomial presentations.
   Localize its isomorphism again at the prime: if `N = (I/I²)_q`, it yields
   `N ⊕ S_q^m ≅ S_q^(t+n)`; successive module localizations identify its first term with `N`.
6. This makes `N` a finite projective module, hence flat by projective-module-flat.
   Finite-flat-local-free gives freeness. Reduction to the residue field computes the
   basis cardinality as `t + n - m = n - d`, hence also `0 ≤ d ≤ n`.
-/
theorem exists_basis_cotangent_localization_of_completeIntersection
    {k : Type u} [Field k] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) k))
    (q : PrimeSpectrum (MvPolynomial (Fin n) k ⧸ I))
    (hci : ∃ g : MvPolynomial (Fin n) k ⧸ I,
      g ∉ q.asIdeal ∧ Algebra.IsGlobalCompleteIntersection k (Localization.Away g)) :
    ∃ d : ℕ, topologicalKrullDimAt q = (d : WithBot ℕ∞) ∧ d ≤ n ∧
      Nonempty (Module.Basis (Fin (n - d)) (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl I.Cotangent)) := by
  classical
  obtain ⟨g, m, t, f, hg, htm, ⟨e⟩, hdim, hdimAt⟩ :=
    principal_ci_presentation_dimension n I q hci
  obtain ⟨E⟩ := stable_conormal_of_completeIntersection_presentation
    n I q g hg m t f htm e hdim
  obtain ⟨hmt, ⟨b⟩⟩ := basis_of_stably_free m (t + n) E
  refine ⟨m - t, hdimAt, ?_, ?_⟩
  · omega
  · have heq : (t + n) - m = n - (m - t) := by omega
    exact ⟨(b.reindex (finCongr heq))⟩

end Ideal
