/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.Paper.LisseQlbarRepresentationDefs

/-! # Integral lattices on normal schemes

Source: the representation theorem, clause (4).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonObj Opposite
open scoped TensorProduct CategoryTheory.Obj
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  AlgebraicGeometry.ProEtale.monoidal_upperStarFromPoint
namespace AlgebraicGeometry.ProEtale.LisseRepresentation

attribute [local irreducible] IntegralNormalization Compatibilities FiniteFreeFibre

/-- A lisse finite-extension coefficient module on a connected normal Noetherian
scheme has an embedded integral lattice. No monodromy correspondence is assumed.

Source: blueprint latest, thm-lisse-qlbar-representations.proof, step 12, clause (4)
(blueprint: lem-sfb-normal-lisse-finite-coefficient-lattice).

Proof: transport the condensed coefficients and L to continuous-function coefficient
sheaves using the canonical coefficient comparisons, which intertwine the integral
inclusion. The lattice-class sheaf is locally constant and locally nonempty, and a
section gives an actual locally finite free lattice pair. Since X is nonempty, connected,
normal and Noetherian, the normal locally constant finite-section theorem gives a finite
etale surjection on which this sheaf has a section. Take its lattice pair there. The
finite-etale lattice-descent theorem applies because a locally Noetherian quasi-compact
scheme has Noetherian underlying space; it produces an integral finite locally free
model on X whose localization is L. The embedded-lattice coefficient comparison turns
this pair into a monomorphism into L, with invertible scalar-extension adjoint. Transport
back to internal modules. Local finite free charts show that the lattice is lisse,
including on zero-rank components. This gives exactly HasLattice, with no separatedness
or invertibility hypothesis on ell.
-/
theorem has_lattice_of_normal
    (ell : ℕ) [Fact ell.Prime]
    (X : Scheme.{u}) [Nonempty X] [ConnectedSpace X] [IsLocallyNoetherian X] [CompactSpace X]
    (hnormal : ∀ z : X, IsDomain (X.presheaf.stalk z) ∧
      IsIntegrallyClosed (X.presheaf.stalk z))
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (L : Modules (Mon.mk (Profinite.continuousMapRingObj E)) X)
    (hL : IsLisseCoefficientModule (Profinite.continuousMapRingObj E) L) :
    HasLattice ell E X L := by sorry

end AlgebraicGeometry.ProEtale.LisseRepresentation
