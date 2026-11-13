/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# The spectrum of a finite free algebra
-/

@[expose] public section

universe u v

namespace AlgebraicGeometry

/-- The spectrum of an algebra admitting a finite module basis is finite locally free.
No nonzero-ring or Noetherian hypothesis is needed, and the index type may be empty. -/
theorem specMap_isFiniteLocallyFree_of_basis
    (A S : Type u) [CommRing A] [CommRing S] [Algebra A S]
    {I : Type v} [Finite I] (_b : Module.Basis I A S) :
    (Spec.map (CommRingCat.ofHom (algebraMap A S))).IsFiniteLocallyFree := by
  have : Module.Free A S := Module.Free.of_basis _b
  have : Module.Finite A S := Module.Finite.of_basis _b
  have : Module.FinitePresentation A S := Module.finitePresentation_of_projective A S
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap A S))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap A S))) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap A S))) := by
    rw [LocallyOfFinitePresentation.SpecMap_iff]
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  exact {}

end AlgebraicGeometry
