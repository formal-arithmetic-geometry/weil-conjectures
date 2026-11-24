/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.FieldTheory.FinTrdeg
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import WeilConjectures.FieldTheory.FinitelyGeneratedFieldCompleteIntersectionModel
import WeilConjectures.RingTheory.FractionFieldCompleteIntersectionCotangent

/-!
# Cartier equality

## References

* Stacks Project, Tag 07E1
-/

@[expose] public section

universe u v

open Algebra

/-! The theorem below is the Cartier dimension formula for a finitely generated
field extension. -/
/--
For a finitely generated field extension, the Kähler differentials and the first homology of
the naive cotangent complex are finite-dimensional, and `trdeg + dim H₁ = dim Ω` in `Cardinal`.
In particular the dimensions agree for a finite extension (Stacks, Tag 07E1). -/
theorem cartier_equality
    (k K : Type*) [Field k] [Field K] [Algebra k K]
    (hfg : IntermediateField.FG (⊤ : IntermediateField k K)) :
    Module.Finite K (KaehlerDifferential k K) ∧
      Module.Finite K (Algebra.H1Cotangent k K) ∧
      Algebra.trdeg k K + Module.finrank K (Algebra.H1Cotangent k K) =
        Module.finrank K (KaehlerDifferential k K) ∧
      (FiniteDimensional k K →
        Module.finrank K (KaehlerDifferential k K) =
          Module.finrank K (Algebra.H1Cotangent k K)) := by
  classical
  -- The finite basis and complete-intersection model provide the required coordinates.
  have : Algebra.EssFiniteType k K := IntermediateField.fg_top_iff.mp hfg
  obtain ⟨s, hs⟩ := exists_finset_isTranscendenceBasis k K
  let x : Fin s.card → K := fun i ↦ (s.equivFin.symm i : K)
  have hx : IsTranscendenceBasis k x := hs.comp_equiv s.equivFin.symm
  have hgens : ∃ (m : ℕ) (b : Fin m → K),
      IntermediateField.adjoin k (Set.range b) = ⊤ := by
    obtain ⟨t, ht⟩ := hfg
    refine ⟨t.card, fun i ↦ (t.equivFin.symm i : K), ?_⟩
    have hr : Set.range (fun i ↦ (t.equivFin.symm i : K)) = (t : Set K) := by
      change Set.range (Subtype.val ∘ t.equivFin.symm) = _
      rw [EquivLike.range_comp, Subtype.range_coe]
    rwa [hr]
  obtain ⟨n, c, f, hcn, hnc, hlen, hreg, _, _, _, hA, e, _⟩ :=
    FieldTheory.exists_completeIntersection_fractionField_model k K hgens s.card x hx
  obtain ⟨δ, ⟨eH⟩, ⟨eΩ⟩⟩ :=
    exists_fractionField_completeIntersection_cotangent_model k K n f hreg e
  have hH : Module.Finite K (H1Cotangent k K) := Module.Finite.equiv eH.symm
  have hΩ : Module.Finite K (KaehlerDifferential k K) := Module.Finite.equiv eΩ.symm
  have hker := δ.finrank_range_add_finrank_ker
  have hcoker := (LinearMap.range δ).finrank_quotient_add_finrank
  simp only [Module.finrank_fin_fun] at hker
  have hker := hker.trans hlen
  rw [Module.finrank_fin_fun] at hcoker
  have hdim : s.card + Module.finrank K (H1Cotangent k K) =
      Module.finrank K (KaehlerDifferential k K) := by
    rw [eH.finrank_eq, eΩ.finrank_eq]
    omega
  have htrdeg : Algebra.trdeg k K = (s.card : Cardinal) := by
    simpa using hs.cardinalMk_eq_trdeg.symm
  have heq : Algebra.trdeg k K + Module.finrank K (H1Cotangent k K) =
      Module.finrank K (KaehlerDifferential k K) := by
    rw [htrdeg, ← Nat.cast_add, hdim]
  refine ⟨hΩ, hH, heq, ?_⟩
  intro hfinite
  -- Substitute zero transcendence degree, then cancel the natural-number casts.
  let _ : FiniteDimensional k K := hfinite
  have hzero : Algebra.trdeg k K = 0 := by
    exact trdeg_eq_zero
  rw [hzero, zero_add] at heq
  -- The cardinal equality specializes to the finite-dimensional equality.
  exact_mod_cast heq.symm
