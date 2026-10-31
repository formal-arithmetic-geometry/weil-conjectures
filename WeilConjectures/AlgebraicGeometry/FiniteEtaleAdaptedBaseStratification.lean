/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Limits

import WeilConjectures.AlgebraicGeometry.FiniteEtaleBaseClopenStratification
import WeilConjectures.AlgebraicGeometry.FiniteEtaleBaseClopenFactorization

/-!
# Base stratification adapted to a finite etale map

Source: Stacks Project, Tag 095H, `lemma-pushforward-constructible`, split-cover argument;
Tags 09Y4 and 04HN, and the geometric generic-interiors argument in the latest blueprint,
`lem-weil-pbc-finite-pushforward-generic-constructible`, first three proof paragraphs.
The scheme-theoretic refinement is the agent assembly recorded in the DAG
(blueprint: lem-a1-finite-etale-adapted-base-stratification).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A finite etale map over a Noetherian base admits a finite reduced base stratification
whose source pullbacks split into clopen pieces indexed by the supplied source strata.
Each piece factors through its original scheme stratum, and has exactly its inverse image
as underlying subset. Empty components are allowed.

Source: Stacks Project, Tags 095H, 09Y4 and 04HN, with the agent geometric refinement
recorded in the DAG (blueprint: lem-a1-finite-etale-adapted-base-stratification).

Proof:
1. Apply `finite_etale_exists_base_clopen_stratification`
   (lem-a1-finite-etale-base-clopen-stratification): Noetherian induction on closed subsets
   of `Y` with reduced induced structures, and on an integral affine Noetherian piece the
   removal of the finite image of the complement of the generic-fibre stratum interiors,
   give reduced base strata `T_a`, open and closed pieces `C_{a,i}` of `X ×_Y T_a` forming a
   coproduct, and the range equations `range j_{a,i} = pr_1⁻¹(S_i)`.
2. For each `a` and `i` apply `finite_etale_clopen_piece_factors_through_source_stratum`
   (lem-a1-finite-etale-base-clopen-factorization): `X ×_Y T_a` is etale over the reduced
   `T_a`, hence reduced, so is its open piece `C_{a,i}`; factor `s_i` as a closed immersion
   followed by an open one, lift through the open part by the range equation and through the
   closed part by the reduced-source factorization. This gives `v_{a,i}` with
   `s_i v_{a,i} = pr_1 j_{a,i}`; the range equations are kept from step 1.
   No surjectivity of `f` is used; an empty restricted source has all `C_{a,i}` empty. -/
theorem finite_etale_exists_adapted_base_stratification
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Etale f]
    [IsLocallyNoetherian Y] [CompactSpace Y] (S : FiniteLocallyClosedStratification X) :
    ∃ T : FiniteLocallyClosedStratification Y,
      (∀ a : Fin T.n, IsReduced (T.domain a)) ∧
      ∀ a : Fin T.n,
        ∃ (C : Fin S.n → Scheme.{u})
          (j : ∀ i : Fin S.n, C i ⟶ pullback f (T.immersion a)),
          (∀ i : Fin S.n, IsOpenImmersion (j i) ∧ IsClosedImmersion (j i)) ∧
          Nonempty (IsColimit (Cofan.mk (pullback f (T.immersion a)) j)) ∧
          ∀ i : Fin S.n,
            (∃ v : C i ⟶ S.domain i,
              v ≫ S.immersion i = j i ≫ pullback.fst f (T.immersion a)) ∧
            Set.range (j i) = (pullback.fst f (T.immersion a)) ⁻¹' S.stratum i  := by
  obtain ⟨T, hTred, hT⟩ := finite_etale_exists_base_clopen_stratification f S
  refine ⟨T, hTred, ?_⟩
  intro a
  obtain ⟨C, j, hj, hc, hr⟩ := hT a
  refine ⟨C, j, hj, hc, ?_⟩
  intro i
  exact ⟨finite_etale_clopen_piece_factors_through_source_stratum f S a
    (hTred a) C j hj hr i, hr i⟩

end AlgebraicGeometry.Scheme
