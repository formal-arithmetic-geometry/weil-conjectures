/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.KrullDimension
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.AffineComplementReciprocalCover
import WeilConjectures.AlgebraicGeometry.ReciprocalCoverLineBundle
import WeilConjectures.AlgebraicGeometry.InvertibleGeneratingSectionsFibre

/-! # Globally generated invertible modules with a prescribed affine section locus

Specialized to Noetherian integral separated schemes of dimension one.

## References

* Stacks Project, Varieties, Lemma 09NB.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A nonempty affine open with finite complement in an integral separated Noetherian
one-dimensional scheme is the nonvanishing locus of a section of a globally generated
invertible module (Stacks, Tag 09NB). -/
theorem exists_globallyGenerated_invertible_nonvanishing_eq
    (X : Scheme.{u}) [IsIntegral X] [X.IsSeparated] [IsLocallyNoetherian X]
    [CompactSpace X] (hdim : topologicalKrullDim X = 1) (U : X.Opens)
    (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty)
    (hfin : (Set.compl (U : Set X)).Finite) :
    ∃ L : X.Modules, L.IsInvertible ∧ Nonempty (SheafOfModules.GeneratingSections L) ∧
      ∃ s : L.val.presheaf.obj (Opposite.op ⊤), nonvanishingLocus L s = (U : Set X) := by
  classical
  obtain ⟨V, f, g, hcover, hinv, hlocus⟩ :=
    exists_affine_complement_reciprocal_cover X hdim U hU hne hfin
  obtain ⟨L, s, t, hL, hs, ht⟩ :=
    exists_line_bundle_sections_of_reciprocal_cover X U V f g hcover hinv hlocus
  have : L.IsInvertible := hL
  let a : ULift.{u} (Fin 2) → L.sections := fun i ↦ if i.down = 0 then s else t
  have ha : CategoryTheory.Epi (L.freeHomEquiv.symm a) :=
    (invertible_generating_sections_fibre_criterion X L 1 a).1.mpr (by
      intro x
      have hx : x ∈ U ⊔ V := by rw [hcover]; trivial
      rcases hx with hx | hx
      · refine ⟨⟨0⟩, ?_⟩
        simpa only [a, ↓reduceIte, hs] using hx
      · refine ⟨⟨1⟩, ?_⟩
        simpa [a] using ht hx)
  exact ⟨L, hL, ⟨{ I := ULift.{u} (Fin 2), s := a, epi := ha }⟩,
    s.val (Opposite.op ⊤), hs⟩

end AlgebraicGeometry.Scheme.Modules
