/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
import Sheaf.RingTheory.IsStrictHenselization
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Noetherianity and faithful flatness of the completed strict henselization

Source: Stacks Project, More on Algebra, Lemma Tag 06LJ, parts (a) and (c), and
Algebra, Lemma Tag 00HR (blueprint: lem-sc-strict-henselization-completion-noetherian).
-/

universe u

namespace Algebra

/-- The completion of the strict henselization of a Noetherian local ring at the extended
maximal ideal is Noetherian, and the canonical completion map is local and faithfully flat.
Source: Stacks Project, Tag 06LJ, parts (a) and (c), and Tag 00HR
(blueprint: lem-sc-strict-henselization-completion-noetherian).

Proof:
1. Put `I = m C`. The strict henselization triples theorem
`lem-weil-pbc-strict-henselization-triples` identifies `C` as local with maximal ideal `I`
and residue field `K`. Noetherianity of `A` makes `m`, hence `I`, finitely generated.
The quotient `C/I` is a field and is Noetherian. The completion criterion
`lem-weil-pbc-completion-noetherian-quotient-noetherian` now makes the completion Noetherian.
2. The completion map is flat by `lem-sc-strict-henselization-completion-flat`.
3. Projection of the completion to `C/I` has kernel precisely the nonunits: a compatible
sequence with nonzero first coordinate is a unit in every `C/I^n`, and the inverses are
compatible by uniqueness. Thus the completion is local. The composite of the completion
map and this projection is the quotient map, so the completion map reflects units and
is local.
4. Flatness and locality imply faithful flatness by
`lem-pc-local-flat-faithful-flat-reflects-surjective` (Tag 00HR). -/
theorem strictHenselization_completion_noetherian_faithfullyFlat
    (A K C : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing C] [Algebra A C] (hC : IsStrictHenselization A K C) :
    IsNoetherianRing
        (AdicCompletion ((IsLocalRing.maximalIdeal A).map (algebraMap A C)) C) ∧
      IsLocalHom (algebraMap C
        (AdicCompletion ((IsLocalRing.maximalIdeal A).map (algebraMap A C)) C)) ∧
      Module.FaithfullyFlat C
        (AdicCompletion ((IsLocalRing.maximalIdeal A).map (algebraMap A C)) C) := by
  sorry

end Algebra
