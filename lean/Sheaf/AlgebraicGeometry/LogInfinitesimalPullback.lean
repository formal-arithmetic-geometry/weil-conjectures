/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.AlgebraicGeometry.StrictLogPullbackUniversal
/-!
# Etale-local logarithmic lifts in a log fibre product
Source: Kato 3.2--3.3; ILO VIII 3.3.5--3.3.6
(blueprint: lem-sfb-log-infinitesimal-pullback).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

private theorem compEq_iff {X Y Z : Scheme.{u}}
    {L : EtaleLogStructure X} {M : EtaleLogStructure Y} {N : EtaleLogStructure Z}
    (a : EtaleLogMap L M) (b : EtaleLogMap M N) (c : EtaleLogMap L N) :
    a.CompEq b c ↔ c = a.comp b := by
  constructor
  · exact EtaleLogMap.eq_comp_of_compEq
  · intro hc
    rw [hc]
    exact a.comp_compEq b

private theorem compositesEq_iff {T X X' Y : Scheme.{u}}
    {L : EtaleLogStructure T} {M : EtaleLogStructure X}
    {M' : EtaleLogStructure X'} {N : EtaleLogStructure Y}
    (a : EtaleLogMap L M) (f : EtaleLogMap M N)
    (i : EtaleLogMap L M') (b : EtaleLogMap M' N) :
    a.CompositesEq f i b ↔ a.comp f = i.comp b := by
  constructor
  · rintro ⟨d, ha, hi⟩
    exact (EtaleLogMap.eq_comp_of_compEq ha).symm.trans
      (EtaleLogMap.eq_comp_of_compEq hi)
  · intro he
    refine ⟨a.comp f, a.comp_compEq f, ?_⟩
    rw [he]
    exact i.comp_compEq b

private theorem pullback_hom_ext {X X' Y Y' T : Scheme.{u}}
    {M : EtaleLogStructure X} {M' : EtaleLogStructure X'}
    {N : EtaleLogStructure Y} {N' : EtaleLogStructure Y'} {L : EtaleLogStructure T}
    {p : EtaleLogMap M' M} {q : EtaleLogMap M' N'}
    {f : EtaleLogMap M N} {h : EtaleLogMap N' N}
    (hu : p.IsLogPullback q f h) (hs : p.comp f = q.comp h)
    (a b : EtaleLogMap L M') (hp : a.comp p = b.comp p) (hq : a.comp q = b.comp q) :
    a = b := by
  have hs' : (a.comp p).comp f = (a.comp q).comp h := by
    rw [a.comp_assoc, hs, ← a.comp_assoc]
  obtain ⟨c, _, hc⟩ := hu T L (a.comp p) (a.comp q) hs'
  exact (hc a ⟨rfl, rfl⟩).trans (hc b ⟨hp.symm, hq.symm⟩).symm

/-- Etale-local infinitesimal lifts are preserved by a log fibre product.
Source: Kato 3.2--3.3; ILO VIII 3.3.5--3.3.6
(blueprint: lem-sfb-log-infinitesimal-pullback).
Proof: project the test square to X and Y and take an etale-local lift to X.
Pair it with the fixed map to Y' by the log product property. The restriction of
this pairing is the prescribed top map because both projections agree. The test
objects and their strict etale maps are the ones supplied by the original lift. -/
theorem EtaleLogMap.localLifts_pullback {X X' Y Y' : Scheme.{u}}
    {M : EtaleLogStructure X} {M' : EtaleLogStructure X'}
    {N : EtaleLogStructure Y} {N' : EtaleLogStructure Y'}
    (p : EtaleLogMap M' M) (q : EtaleLogMap M' N')
    (f : EtaleLogMap M N) (h : EtaleLogMap N' N)
    (hs : p.comp f = q.comp h) (hu : p.IsLogPullback q f h)
    (hf : f.HasEtaleLocalInfinitesimalLifts) : q.HasEtaleLocalInfinitesimalLifts := by
  intro T₀ T L₀ L hL₀ hL i a b hi his hab t
  have hab' := (compositesEq_iff a q i b).mp hab
  have htest : (a.comp p).CompositesEq f i (b.comp h) := by
    apply (compositesEq_iff _ _ _ _).mpr
    rw [a.comp_assoc, hs, ← a.comp_assoc, hab', i.comp_assoc]
  obtain ⟨V, L', v, c, L₀', v₀, j, ht, hv, hvs, hv₀, hv₀s, hj,
    hjv, hcf, hjc⟩ := hf T₀ T L₀ L hL₀ hL i (a.comp p) (b.comp h) hi his htest t
  have hjv' := (compositesEq_iff _ _ _ _).mp hjv
  have hcf' := (compositesEq_iff _ _ _ _).mp hcf
  have hjc' := (compositesEq_iff _ _ _ _).mp hjc
  have hpair : c.comp f = (v.comp b).comp h := by
    rw [v.comp_assoc]
    exact hcf'
  obtain ⟨d, ⟨hdp, hdq⟩, _⟩ := hu V.left L' c (v.comp b) hpair
  refine ⟨V, L', v, d, L₀', v₀, j, ht, hv, hvs, hv₀, hv₀s, hj, hjv, ?_, ?_⟩
  · exact (compositesEq_iff _ _ _ _).mpr hdq
  · apply (compositesEq_iff _ _ _ _).mpr
    apply pullback_hom_ext hu hs
    · rw [j.comp_assoc, hdp, hjc', ← v₀.comp_assoc]
    · rw [j.comp_assoc, hdq, ← j.comp_assoc, hjv', v₀.comp_assoc,
        ← hab', ← v₀.comp_assoc]
end AlgebraicGeometry
