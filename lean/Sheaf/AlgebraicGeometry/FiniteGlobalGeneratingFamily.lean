/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Sheaf.AlgebraicGeometry.FiniteSectionsCover
import Sheaf.AlgebraicGeometry.InvertibleGeneratingSectionsFibre

/-! # Finite global generating families for invertible modules

Source: Stacks Project, Varieties, Tag 09NC; Modules, Tag 01AO.
-/

@[expose] public section

universe v

namespace AlgebraicGeometry.Scheme.Modules

/-- A globally generated invertible module on a quasi-compact scheme admits a finite global
family of generators. Source: Stacks Project, Varieties, Tag 09NC, proof; Modules, Tag 01AO.
(blueprint: lem-sc-finite-global-generating-family).

Proof: start with any global generating family. At each point its germs generate the
rank-one stalk. Trivialize the stalk and reduce modulo its maximal ideal; at least one
coefficient is nonzero, so that coefficient is a unit in the local ring. Thus some family
member generates the stalk. The locus on which that section generates is open: shrink a
local trivialization until the coefficient is invertible. These opens cover the scheme.
Quasi-compactness gives a finite subcover. The corresponding finite subfamily generates
all stalks, so its free sheaf map is epimorphic by the stalkwise surjectivity criterion.
This also handles the empty scheme, where the empty family generates the zero sheaf. -/
theorem finite_global_generating_family
    (X : Scheme.{v}) [CompactSpace X] (L : X.Modules) (hL : L.IsInvertible)
    (hG : Nonempty (SheafOfModules.GeneratingSections L)) :
    ∃ σ : SheafOfModules.GeneratingSections L, σ.IsFiniteType := by
  classical
  let := hL
  obtain ⟨m, t, ht⟩ := finite_sections_cover_of_globally_generated X L hG
  let s : ULift.{v} (Fin (m + 1)) → L.sections := fun i ↦
    PresheafOfModules.sectionsMk
      (fun U ↦ L.val.map (CategoryTheory.homOfLE le_top).op
        (Fin.lastCases 0 t i.down))
      (fun {_ _} f ↦ by
        rw [← L.val.map_comp_apply]
        congr 1)
  have hs : CategoryTheory.Epi (L.freeHomEquiv.symm s) := by
    apply (invertible_generating_sections_fibre_criterion X L m s).1.mpr
    intro x
    have hx : x ∈ ⋃ j, nonvanishingLocus L (t j) := by rw [ht]; trivial
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    refine ⟨⟨j.castSucc⟩, ?_⟩
    simpa [s] using hj
  exact ⟨{ I := ULift.{v} (Fin (m + 1)), s := s, epi := hs }, ⟨inferInstance⟩⟩

end AlgebraicGeometry.Scheme.Modules
