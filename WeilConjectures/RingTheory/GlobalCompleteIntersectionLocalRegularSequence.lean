/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Regular.Flat
import WeilConjectures.RingTheory.IsRegularOfDimensionDrop
import WeilConjectures.RingTheory.PolynomialRingMaximalLocalizationDimension
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# Equations of a global complete intersection at a prime

For a nonzero quotient of an `m`-variable polynomial ring over a field by `t` equations, of
dimension `m - t`, the equations form a regular sequence after localization at any prime
containing them.

## Implementation details

First localize at a maximal ideal containing the prime: this is a regular local ring of
dimension `m`, the local quotient has dimension exactly `m - t` (height bound and comparison
with the global dimension), so the equations form a regular sequence by the Cohen-Macaulay
dimension-drop criterion. Regularity then passes to the further localization at the prime.

## References

* [Stacks, Tag 00SB]
* [Stacks, Tag 00SC]
-/

@[expose] public section

universe u

namespace MvPolynomial

/-- For a nonzero quotient of an `m`-variable polynomial ring by `t` equations of dimension
`m - t`, the equations form a regular sequence after localization at any prime containing
these equations. The dimension hypothesis is written additively, avoiding truncated
subtraction when `t > m`. -/
theorem isRegular_localizationAtPrime_of_quotient_dimension
    (k : Type u) [Field k] (m t : ℕ) (f : Fin t → MvPolynomial (Fin m) k)
    [Nontrivial (MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range f))]
    (hdim : topologicalKrullDim
      (AlgebraicGeometry.Spec
        (CommRingCat.of (MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range f)))) +
      (t : WithBot ℕ∞) = (m : WithBot ℕ∞))
    (q : Ideal (MvPolynomial (Fin m) k)) [q.IsPrime]
    (hq : Ideal.span (Set.range f) ≤ q) :
    RingTheory.Sequence.IsRegular (Localization.AtPrime q)
      ((List.ofFn f).map (algebraMap (MvPolynomial (Fin m) k) (Localization.AtPrime q))) := by
  classical
  let Q := MvPolynomial (Fin m) k
  let fs := List.ofFn f
  let J := Ideal.span (Set.range f)
  -- The ordered list and the given family generate the same ideal.
  have hfs : Ideal.ofList fs = J := by
    change Ideal.span {x | x ∈ fs} = J
    congr 1
    ext x
    simp [fs]
  obtain ⟨M, hM, hqM⟩ := Ideal.exists_le_maximal q Ideal.IsPrime.ne_top'
  let := hM
  let R := Localization.AtPrime M
  have : IsRegularLocalRing R := inferInstance
  let gs := fs.map (algebraMap Q R)
  have hmem : ∀ g ∈ gs, g ∈ IsLocalRing.maximalIdeal R := by
    intro g hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    apply (IsLocalization.AtPrime.to_map_mem_maximal_iff R M a).mpr
    exact hqM (hq (by
      change a ∈ J
      rw [← hfs]
      exact Ideal.subset_span ha))
  have hd : ringKrullDim R = (m : WithBot ℕ∞) :=
    ringKrullDim_localizationAtMaximal m M
  obtain ⟨s, hcard, hs⟩ :=
    (IsNoetherian.noetherian (IsLocalRing.maximalIdeal R)).exists_span_finset_card_eq_spanFinrank
  let rs := s.toList
  have hspan : Ideal.span {x | x ∈ rs} = IsLocalRing.maximalIdeal R := by
    simpa [rs] using hs
  have hlen : rs.length = m := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
    rw [hd] at h
    have hrank : (IsLocalRing.maximalIdeal R).spanFinrank = m := by exact_mod_cast h
    simp [rs, hcard, hrank]
  have hparams : IsLocalRing.IsRegularSystemOfParameters rs :=
    ⟨hspan, by rw [hlen, hd]⟩
  have hreg := (IsRegularLocalRing.isRegular_and_quotients_of_generators
    R m hd rs hparams).1
  -- A regular system of parameters witnesses the required depth bound.
  have hdepth : (m : ℕ∞) ≤ IsLocalRing.depth (R := R) R := by
    unfold IsLocalRing.depth Ideal.depth
    split_ifs
    · exact le_top
    · apply le_sSup
      refine ⟨rs, hreg, ?_, ?_⟩
      · intro x hx
        rw [← hspan]
        exact Ideal.subset_span hx
      · rw [hlen]
  have hlength : gs.length = t := by simp [gs, fs]
  -- Squeeze the local quotient dimension between the height bound and global dimension.
  have hlower : (m : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ Ideal.ofList gs) + t := by
    have h := ringKrullDim_le_ringKrullDim_quotient_add_card gs.toFinset (by
      intro x hx
      rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
      exact hmem x (by simpa using hx))
    have he : Ideal.span (gs.toFinset : Set R) = Ideal.ofList gs := by
      congr 1
      ext x
      simp
    rw [hd, he] at h
    exact h.trans (add_le_add le_rfl (by exact_mod_cast
      ((List.toFinset_card_le gs).trans_eq hlength)))
  have hupper : ringKrullDim (R ⧸ Ideal.ofList gs) ≤ ringKrullDim (Q ⧸ J) := by
    rw [ringKrullDim_quotient, ringKrullDim_quotient]
    let e : PrimeSpectrum.zeroLocus (R := R) (Ideal.ofList gs) ↪o
        PrimeSpectrum.zeroLocus (R := Q) J := {
      toFun := fun p => ⟨PrimeSpectrum.comap (algebraMap Q R) p.1, by
        change J ≤ p.1.asIdeal.comap (algebraMap Q R)
        rw [← hfs, Ideal.map_le_iff_le_comap.symm, Ideal.map_ofList]
        exact p.2⟩
      inj' := by
        intro p p' h
        apply Subtype.ext
        apply PrimeSpectrum.ext
        exact (IsLocalization.orderEmbedding M.primeCompl R).injective
          (congrArg (fun p => p.1.asIdeal) h)
      map_rel_iff' := by
        intro p p'
        exact (IsLocalization.orderEmbedding M.primeCompl R).le_iff_le }
    exact Order.krullDim_le_of_orderEmbedding e
  have hglobal : ringKrullDim (Q ⧸ J) + (t : WithBot ℕ∞) = m := by
    change topologicalKrullDim (PrimeSpectrum (Q ⧸ J)) + _ = _ at hdim
    rwa [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at hdim
  have hdrop : ringKrullDim (R ⧸ Ideal.ofList gs) +
      (gs.length : WithBot ℕ∞) = (m : WithBot ℕ∞) := by
    rw [hlength]
    exact le_antisymm ((add_le_add hupper le_rfl).trans_eq hglobal) hlower
  have hregular := RingTheory.Sequence.isRegular_of_dimension_drop m hd hdepth gs hmem hdrop
  -- Localize R directly into Q_q; no choice of an iterated-localization isomorphism.
  let S := Localization.AtPrime q
  have hle : M.primeCompl ≤ q.primeCompl := fun x hx hxq => hx (hqM hxq)
  let : Algebra R S := IsLocalization.localizationAlgebraOfSubmonoidLe R S
    M.primeCompl q.primeCompl hle
  let : IsScalarTower Q R S := IsLocalization.localization_isScalarTower_of_submonoid_le
    R S M.primeCompl q.primeCompl hle
  let : IsLocalization (q.primeCompl.map (algebraMap Q R)) S :=
    IsLocalization.isLocalization_of_submonoid_le R S M.primeCompl q.primeCompl hle
  have hweak := hregular.1.of_isLocalization S (q.primeCompl.map (algebraMap Q R))
  have hmap : gs.map (algebraMap R S) = fs.map (algebraMap Q S) := by
    simp only [gs, List.map_map]
    congr 1
    exact congrArg (fun h : Q →+* S => (h : Q → S))
      (IsScalarTower.algebraMap_eq Q R S).symm
  rw [hmap] at hweak
  apply (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal
    (M := S) (fun g hg => ?_)).mpr hweak
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
  apply (IsLocalization.AtPrime.to_map_mem_maximal_iff S q a).mpr
  apply hq
  change a ∈ J
  rw [← hfs]
  exact Ideal.subset_span ha

end MvPolynomial
