/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Properties
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! Scheme-theoretic factorization of clopen pieces through source strata. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A reduced clopen piece of a finite-etale pullback factors through the prescribed source
stratum once its underlying range is the corresponding inverse image.

Source: Stacks Project, Tag 0356 and the factorization paragraph of Tag 095H
(blueprint: lem-a1-finite-etale-base-clopen-factorization).

Proof: etaleness over a reduced base makes the pullback reduced, and an open subscheme of a
reduced scheme is reduced. Factor the prescribed immersion as a closed immersion followed by
an open immersion; range containment first factors through the open part, then the reduced-source
closed-immersion factorization gives the required map to the source stratum. -/
theorem finite_etale_clopen_piece_factors_through_source_stratum
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Etale f]
    (S : FiniteLocallyClosedStratification X)
    {T : FiniteLocallyClosedStratification Y}
    (a : Fin T.n) (hred : IsReduced (T.domain a))
    (C : Fin S.n → Scheme.{u})
    (j : ∀ i : Fin S.n, C i ⟶ pullback f (T.immersion a))
    (hj : ∀ i : Fin S.n, IsOpenImmersion (j i) ∧ IsClosedImmersion (j i))
    (hr : ∀ i : Fin S.n,
      Set.range (j i) =
        (pullback.fst f (T.immersion a)) ⁻¹' S.stratum i) :
    ∀ i : Fin S.n,
      ∃ v : C i ⟶ S.domain i,
        v ≫ S.immersion i = j i ≫ pullback.fst f (T.immersion a) := by
  intro i
  have : IsReduced (T.domain a) := hred
  have : IsReduced (pullback f (T.immersion a)) :=
    isReduced_of_etale (pullback.snd f (T.immersion a))
  have : IsOpenImmersion (j i) := (hj i).1
  have : IsReduced (C i) := isReduced_of_isOpenImmersion (j i)
  obtain ⟨Z, c, o, hc, ho, hco⟩ :=
    IsImmersion.isImmersion_iff_exists.mp (S.isImmersion i)
  have : IsClosedImmersion c := hc
  have : IsOpenImmersion o := ho
  let g := j i ≫ pullback.fst f (T.immersion a)
  have hg : Set.range g ⊆ Set.range (S.immersion i) := by
    rintro _ ⟨x, rfl⟩
    rw [S.range_immersion]
    exact (hr i ▸ (Set.mem_range_self x) : j i x ∈
      (pullback.fst f (T.immersion a)) ⁻¹' S.stratum i)
  have hgo : Set.range g ⊆ Set.range o := by
    rw [← hco] at hg
    rintro x hx
    obtain ⟨z, hz⟩ := hg hx
    exact ⟨c z, by simpa only [Scheme.Hom.comp_apply] using hz⟩
  let g' := IsOpenImmersion.lift o g hgo
  have hg' : g' ≫ o = g := IsOpenImmersion.lift_fac o g hgo
  have hgc : Set.range g'.base ⊆ Set.range c.base := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨z, hz⟩ := hg (Set.mem_range_self x)
    refine ⟨z, o.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hco, hg']
    exact hz
  obtain ⟨v, hv, -⟩ :=
    IsClosedImmersion.existsUnique_fac_of_range_subset_range c g' hgc
  refine ⟨v, ?_⟩
  rw [← hco, ← Category.assoc, hv]
  exact hg'

end AlgebraicGeometry.Scheme
