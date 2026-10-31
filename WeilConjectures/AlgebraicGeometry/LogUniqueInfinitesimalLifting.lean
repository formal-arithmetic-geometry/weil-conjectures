/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.LogMorphismOperations
public import WeilConjectures.AlgebraicGeometry.LogInfinitesimalLifting
/-!
# Identities and composition preserve unique logarithmic infinitesimal lifts

Source: Kato 1988, 3.1--3.3; ILO X 1.2
(blueprint: lem-sfb-log-unique-lifting-composition).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
/-- The identity has exactly one lift for every strict square-zero test square.
Source: Kato 3.1--3.3 (blueprint: lem-sfb-log-unique-lifting-composition).
Proof: the given bottom map is the lift, and the equation with the identity forces
any other lift to equal it. -/
theorem EtaleLogMap.uniqueLifts_id {X : Scheme.{u}} (M : EtaleLogStructure X) :
    (EtaleLogMap.id M).HasUniqueInfinitesimalLifts := by
  intro T₀ T L₀ L _ _ i a b _ _ hsq
  obtain ⟨d, ha, hb⟩ := hsq
  have ha' : d = a := by
    calc
      d = a.comp (EtaleLogMap.id M) := EtaleLogMap.eq_comp_of_compEq ha
      _ = a := a.comp_id
  have hb' : i.CompEq b a := ha' ▸ hb
  refine ⟨b, ⟨b.compEq_id, hb'⟩, ?_⟩
  intro c hc
  calc
    c = c.comp (EtaleLogMap.id M) := c.comp_id.symm
    _ = b := (EtaleLogMap.eq_comp_of_compEq hc.1).symm

/-- Unique logarithmic infinitesimal lifting is stable under composition.
Source: Kato 3.1--3.3 (blueprint: lem-sfb-log-unique-lifting-composition).
Proof: lift first to the intermediate log scheme, then to the source. Any other
lift has the same intermediate composite by uniqueness there, and is then equal
to the chosen lift by uniqueness for the first morphism. -/
theorem EtaleLogMap.uniqueLifts_comp {X Y Z : Scheme.{u}}
    {L : EtaleLogStructure X} {M : EtaleLogStructure Y} {N : EtaleLogStructure Z}
    (f : EtaleLogMap L M) (g : EtaleLogMap M N)
    (hf : f.HasUniqueInfinitesimalLifts) (hg : g.HasUniqueInfinitesimalLifts) :
    (f.comp g).HasUniqueInfinitesimalLifts := by
  intro T₀ T L₀ L' hL₀ hL' i a b hi his hsq
  have hsq' : (a.comp f).CompositesEq g i b := by
    obtain ⟨d, had, hbd⟩ := hsq
    refine ⟨d, ?_, hbd⟩
    have ha := EtaleLogMap.eq_comp_of_compEq had
    rw [ha, ← a.comp_assoc f g]
    exact (a.comp f).comp_compEq g
  obtain ⟨cY, ⟨hcYg, hicY⟩, huniqY⟩ := hg T₀ T L₀ L' hL₀ hL' i (a.comp f) b hi his hsq'
  obtain ⟨cX, ⟨hcXf, hicX⟩, huniqX⟩ :=
    hf T₀ T L₀ L' hL₀ hL' i a cY hi his ⟨a.comp f, a.comp_compEq f, hicY⟩
  refine ⟨cX, ⟨?_, hicX⟩, ?_⟩
  · have hx := EtaleLogMap.eq_comp_of_compEq hcXf
    have hy := EtaleLogMap.eq_comp_of_compEq hcYg
    rw [hy, hx, cX.comp_assoc]
    exact cX.comp_compEq (f.comp g)
  · intro c hc
    have hcf : c.comp f = cY := by
      apply huniqY
      constructor
      · have hcb := EtaleLogMap.eq_comp_of_compEq hc.1
        rw [hcb, ← c.comp_assoc]
        exact (c.comp f).comp_compEq g
      · have hca := EtaleLogMap.eq_comp_of_compEq hc.2
        rw [hca, i.comp_assoc]
        exact i.comp_compEq (c.comp f)
    apply huniqX
    refine ⟨?_, hc.2⟩
    rw [← hcf]
    exact c.comp_compEq f
end AlgebraicGeometry
