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

/-- Every coprojection of the pointed etale algebra presentation becomes flat
when followed by completion at the extended maximal ideal.
Source: Stacks Project, More on Algebra, Tag 06LJ, proof of (c), paragraph
beginning “To finish the proof of (c)”.
(blueprint: lem-sc-pointed-etale-completion-stage-flat).

Proof: Factor the map from a stage `S` to `K` through the residue field at its
kernel `q`. This yields the corresponding etale residue triple. Morphisms
commuting with the maps to `K` are exactly the triple morphisms, so this
identification is an equivalence and carries the algebra colimit to the ring
colimit of triples. The structural map from `R` is preserved. Apply
`lem-sc-etale-triple-to-sh-completion-flat` to that colimit and triple.
Equivalently, localize `S` at `q`, identify its strict henselization with the
vertex, apply completion flatness over the Noetherian local base `S_q`, and
compose with the flat localization `S → S_q`. The extended ideal is the same
under this identification, so the resulting composite is the displayed map. -/
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
  sorry

end Algebra
