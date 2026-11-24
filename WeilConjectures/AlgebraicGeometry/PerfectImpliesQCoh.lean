/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.StrictlyPerfectFiniteFreeRefinement
import WeilConjectures.AlgebraicGeometry.PseudoCoherentQCoh

@[expose] public section

universe u w

open CategoryTheory
namespace AlgebraicGeometry

/-- Perfect complexes have quasi-coherent cohomology (Stacks, Tags 08C4 and 08CM). -/
theorem schemeDerivedQCohProperty_of_isPerfect
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K : schemeDerivedCategory X) (hK : Scheme.IsPerfect X K) :
    schemeDerivedQCohProperty X K := by
  apply Scheme.schemeDerivedQCohProperty_of_isPseudoCoherent X K
  intro x
  obtain ⟨U, hxU, P, hP, hKP⟩ := hK x
  obtain ⟨V, hxV, _, _, F, ⟨a, b, hb⟩, hf, e⟩ :=
    Scheme.exists_finiteFree_refinement_of_isStrictlyPerfect X K U P hP hKP x hxU
  exact ⟨V, hxV, F, ⟨b, fun n hn ↦ hb n (Or.inr hn)⟩, hf, e⟩

end AlgebraicGeometry
