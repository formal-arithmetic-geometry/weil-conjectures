/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
import Sheaf.RingTheory.StrictHenselizationTriples
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.RingHom.Flat

/-!
# Flatness of etale triple maps to the completed strict henselization

Source: Stacks Project, More on Algebra, Tag 06LJ, proof of (c)
(blueprint: lem-sc-etale-triple-to-sh-completion-flat).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Every pointed etale algebra maps flatly to the completion of the strict henselization.
Source: Stacks Project, Tag 06LJ, proof of (c), paragraph beginning
“To finish the proof of (c)” (blueprint: lem-sc-etale-triple-to-sh-completion-flat).

Proof:
1. For a triple `t = (S, q, phi)`, identify the colimit with the strict henselization
of `S_q`, carrying `q S_q` to `m C`, by
`lem-sc-etale-triple-strict-henselization-identification`. This identifies the completions.
2. Etaleness gives finite presentation, hence finite type, by `def-weil-etale-morphism`
and `lem-weil-pbc-lfp-affine-opens-finite-presentation`. Thus `S` is Noetherian by
`lem-weil-pbc-finite-type-algebra-noetherian`, as is `S_q` by
`lem-weil-pbc-localization-noetherian`. Apply
`lem-sc-strict-henselization-completion-flat-over-base` to the Noetherian local ring `S_q`.
3. The localization map `S → S_q` is flat by `lem-weil-pbc-localization-flat`.
Compose with the preceding flat map using `lem-weil-pbc-flat-ring-map-comp`.
The completion identification in step 1 identifies this composite with the displayed map.
-/
theorem etaleTriple_to_strictHenselization_completion_flat
    (R : CommRingCat.{u}) [IsLocalRing R] [IsNoetherianRing R]
    (K : Type u) [Field K]
    [Algebra ((Spec R).residueField ⟨IsLocalRing.maximalIdeal R, inferInstance⟩) K]
    [IsSepClosure ((Spec R).residueField ⟨IsLocalRing.maximalIdeal R, inferInstance⟩) K]
    (c : Cocone (etaleResidueTriplesRingDiagram R
      ⟨IsLocalRing.maximalIdeal R, inferInstance⟩ K
      (CommRingCat.ofHom (algebraMap
        ((Spec R).residueField ⟨IsLocalRing.maximalIdeal R, inferInstance⟩) K))))
    (hc : IsColimit c) (ρ : R ⟶ c.pt)
    (hρ : ∀ t, t.α ≫ c.ι.app t = ρ)
    (t : EtaleResidueTriples R ⟨IsLocalRing.maximalIdeal R, inferInstance⟩ K
      (CommRingCat.ofHom (algebraMap
        ((Spec R).residueField ⟨IsLocalRing.maximalIdeal R, inferInstance⟩) K))) :
    ((algebraMap c.pt
      (AdicCompletion ((IsLocalRing.maximalIdeal R).map ρ.hom) c.pt)).comp
        (c.ι.app t).hom).Flat := by
  sorry

end AlgebraicGeometry.Scheme
