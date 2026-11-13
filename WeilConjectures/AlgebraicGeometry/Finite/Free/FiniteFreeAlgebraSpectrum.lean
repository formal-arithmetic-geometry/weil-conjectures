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
No nonzero-ring or Noetherian hypothesis is needed, and the index type may be empty.

Proof plan:
1. The finitely many basis elements span `S`, so `S` is a finite `A`-module.
The finite ring-map spectrum criterion makes the structural morphism finite.
2. Freeness implies flatness; the affine flatness criterion makes the morphism flat.
3. Write the coordinates of the unit and each product of basis elements. Present an algebra
   on variables indexed by the basis, imposing the unit relation and these multiplication
   relations. Relabel the finite index type by `Fin n`, obtaining finitely many relations
   (def-weil-pbc-finitely-presented-algebra; Stacks Tag 0D46, lemma-finite-finite-type).
4. Evaluation at the basis gives a map from this quotient to `S`. The inverse sends an element
   to the linear combination of the variable classes with its basis coordinates. Uniqueness
   of coordinates gives additivity and linearity; the unit and multiplication relations give
   multiplicativity and preservation of the unit. The two maps are inverse on the basis and
   polynomial generators. For the empty basis, `S` is zero and the unit relation is `1 = 0`,
   so the same construction gives the zero algebra, including when `A` is zero.
5. Use the whole affine source and target as neighbourhoods to obtain local finite
   presentation. Together with steps 1 and 2 this is finite local freeness. -/
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
