/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.RingTheory.IsStrictHenselization
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RingHom.Flat

import Sheaf.RingTheory.EtaleTripleToStrictHenselizationCompletionFlat

/-!
# Flatness from a pointed etale stage to the strict henselization completion

Source: Stacks Project, More on Algebra, Tag 06LJ, proof of (c).
(blueprint: lem-sc-pointed-etale-completion-stage-flat).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace Algebra

/-- The two flat factors in the pointed etale completion map.
Source: Stacks Project, More on Algebra, Tag 06LJ, proof of (c).
(blueprint: new-pointed-etale-completion-stage-flat-factors). -/
theorem pointedEtale_completion_stage_flat_factors
    (R K : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    [IsSepClosure (IsLocalRing.ResidueField R) K] [Algebra R K]
    [IsScalarTower R (IsLocalRing.ResidueField R) K]
    (c : Cocone ((ObjectProperty.ι
      (fun X : Over (CommAlgCat.of R K) ↦ Etale R X.left)) ⋙
        Over.forget (CommAlgCat.of R K)))
    (hc : IsColimit c)
    (t : ObjectProperty.FullSubcategory
      (fun X : Over (CommAlgCat.of R K) ↦ Etale R X.left)) :
    (c.ι.app t).hom.toRingHom.Flat ∧
      (algebraMap c.pt
        (AdicCompletion ((IsLocalRing.maximalIdeal R).map (algebraMap R c.pt)) c.pt)).Flat := by
  sorry

theorem pointedEtale_completion_stage_flat
    (R K : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    [IsSepClosure (IsLocalRing.ResidueField R) K] [Algebra R K]
    [IsScalarTower R (IsLocalRing.ResidueField R) K]
    (c : Cocone ((ObjectProperty.ι
      (fun X : Over (CommAlgCat.of R K) ↦ Etale R X.left)) ⋙
        Over.forget (CommAlgCat.of R K)))
    (hc : IsColimit c)
    (t : ObjectProperty.FullSubcategory
      (fun X : Over (CommAlgCat.of R K) ↦ Etale R X.left)) :
    ((algebraMap c.pt
      (AdicCompletion ((IsLocalRing.maximalIdeal R).map (algebraMap R c.pt)) c.pt)).comp
        (c.ι.app t).hom.toRingHom).Flat := by
  obtain ⟨hstage, hcompletion⟩ := pointedEtale_completion_stage_flat_factors R K c hc t
  exact hstage.comp hcompletion

end Algebra
