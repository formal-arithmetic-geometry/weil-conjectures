/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Topology.Constructible
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluingCore

/-!
# Gluing finite étale constructible stratifications

Source: Stacks Project, Etale Cohomology, `lemma-etale-stratified-finite`, the reduction
"In general, we may assume X is affine".
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- Constructible locally closed partitions with finite étale pullbacks glue over a finite
 affine open cover of a qcqs scheme. Source: Stacks Project, Etale Cohomology,
`lemma-etale-stratified-finite`, locality reduction. -/
theorem exists_constructible_stratification_finite_etale_of_affine_local
    {X U : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace U] [QuasiSeparatedSpace U] (j : U ⟶ X) [Etale j]
    (hlocal : ∃ (n : ℕ) (W : Fin n → X.Opens),
      (∀ a : Fin n, IsAffineOpen (W a)) ∧
      (⋃ a : Fin n, (W a : Set X)) = Set.univ ∧
      ∀ a : Fin n, ∃ S : Stratification (W a),
        (∀ b : Fin S.n, Topology.IsConstructible (S.stratum b)) ∧
        ∀ b : Fin S.n,
          IsFinite (pullback.snd j (S.immersion b ≫ (W a).ι)) ∧
          Etale (pullback.snd j (S.immersion b ≫ (W a).ι))) :
    ∃ S : Stratification X,
      (∀ i : Fin S.n, Topology.IsConstructible (S.stratum i)) ∧
      ∀ i : Fin S.n,
        IsFinite (pullback.snd j (S.immersion i)) ∧
        Etale (pullback.snd j (S.immersion i)) := by
  classical
  obtain ⟨n, W, hW, hcover, hlocal⟩ := hlocal
  choose T hc hf using hlocal
  obtain ⟨S, hS, hfactor⟩ :=
    exists_global_stratification_factoring_local n W hW hcover T hc
  refine ⟨S, hS, ?_⟩
  intro i
  obtain ⟨a, b, q, hq⟩ := hfactor i
  let g := (T a).immersion b ≫ (W a).ι
  have : IsFinite (pullback.snd j g) := (hf a b).1
  have : Etale (pullback.snd j g) := (hf a b).2
  rw [← hq]
  let e := pullbackLeftPullbackSndIso j g q
  have he : e.inv ≫ pullback.snd (pullback.snd j g) q =
      pullback.snd j (q ≫ g) := pullbackLeftPullbackSndIso_inv_snd_snd j g q
  rw [← he]
  exact ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme
