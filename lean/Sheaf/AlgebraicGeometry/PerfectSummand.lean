/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
import Sheaf.AlgebraicGeometry.PerfectPseudoCoherentLocallyFiniteTor
import Sheaf.AlgebraicGeometry.PseudoCoherentSummand
import Sheaf.AlgebraicGeometry.DerivedTensorVanishingRetract
import Sheaf.AlgebraicGeometry.PerfectOfPseudoCoherentLocallyFiniteTor
import all Sheaf.AlgebraicGeometry.SchemeIsoDerivedLocalizations

/-! # Direct summands of perfect complexes

Source: literature/stacks-project/cohomology.tex, Tag 08CS (lemma-summands-perfect)
(blueprint: lem-pc-perfect-summand).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A direct summand of a perfect complex is perfect, and the complementary summand
is perfect as well. First, `lem-pc-perfect-pseudo-coherent-locally-finite-tor` gives
pseudo-coherence and Tor amplitude in an interval on a neighbourhood of each point.
Second, `lem-pc-pseudo-coherent-summand` gives pseudo-coherence of both summands.
Third, both summands are retracts of K; derived pullback, derived tensor and
homology preserve these retracts. The proved
`lem-pc-derived-tensor-vanishing-retract` passes the same local Tor interval
to both summands (Tag 08CK). Finally,
`lem-pc-pseudo-coherent-locally-finite-tor-perfect` constructs perfect models
on affine subopens of the Tor neighbourhoods and gives perfectness on X.
Source: literature/stacks-project/cohomology.tex, Tag 08CS (lemma-summands-perfect)
(blueprint: lem-pc-perfect-summand). -/
theorem perfect_of_directSum
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K L M : schemeDerivedCategory X)
    (h : Nonempty (K ≅ L ⊞ M))
    (hK : IsPerfect X K) :
    IsPerfect X L ∧ IsPerfect X M := by
  classical
  let hOpen (U : X.Opens) :
      HasDerivedCategory.{w}
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
    (hasDerivedCategory_of_equivalence (Modules.overEquiv U).symm).some
  let : ∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) := hOpen
  obtain ⟨hpc, htor⟩ := perfect_isPseudoCoherent_and_hasLocallyFiniteTorDimension X K hK
  obtain ⟨hLpc, hMpc⟩ := pseudoCoherent_of_isIso_biproduct X K L M h hpc
  obtain ⟨e⟩ := h
  let rL : Retract L K :=
    { i := biprod.inl ≫ e.inv
      r := e.hom ≫ biprod.fst
      retract := by simp [Category.assoc] }
  let rM : Retract M K :=
    { i := biprod.inr ≫ e.inv
      r := e.hom ≫ biprod.snd
      retract := by simp [Category.assoc] }
  have tor_of_retract (N : schemeDerivedCategory X) (r : Retract N K) :
      HasLocallyFiniteTorDimension X N := by
    intro x
    obtain ⟨U, hx, a, b, hab, hU⟩ := htor x
    refine ⟨U, hx, a, b, hab, ?_⟩
    intro G i hi
    exact schemeDerivedTensorCohomologyVanishes_of_retract U.toScheme _ _
      (r.map (derivedPullback U.ι)) G i (hU G i hi)
  exact ⟨isPerfect_of_isPseudoCoherent_of_hasLocallyFiniteTorDimension X L hLpc
      (tor_of_retract L rL),
    isPerfect_of_isPseudoCoherent_of_hasLocallyFiniteTorDimension X M hMpc
      (tor_of_retract M rM)⟩

end AlgebraicGeometry.Scheme
