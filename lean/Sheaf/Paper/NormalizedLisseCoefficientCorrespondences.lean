/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.Paper.LisseQlbarRepresentationDefs

/-! # Normalized lisse coefficient correspondences

Source: the representation theorem, clauses (1)--(3).
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

/-- Clauses (1)--(3): normalized integral monodromy, rationalization, and descent
through finite coefficient fields. Normality and the assertion that every continuous
algebraic-closure representation has a finite field of definition are not used here.

Source: blueprint latest, thm-lisse-qlbar-representations.proof, steps 2, 4--11
(blueprint: lem-sfb-normalized-lisse-coefficient-correspondences).

Proof: identify continuous-function and condensed coefficients. Reduce integral lisse
modules modulo positive uniformizer powers and use the integral reduction equivalence.
The finite Galois correspondence applied levelwise equips their fibres with actions.
Its finiteEvaluationAction identifies them all with the same c.γ action on the
underlying set fibres, so coefficient quotient maps intertwine these actions.
The free-point calculation and adic completeness identify the actual fibre with their
inverse limit. The induced action is continuous because its finite quotient actions are.
Full faithfulness follows by taking compatible finite-level maps; effectivity of normalized
finite free towers gives essential surjectivity. The finite fibre comparisons use the
inverse-image/stalk comparisons and are fixed on every pointed etale germ, so the
projections, quotient kernels, scalar actions and complete cone have exactly the specified
normalizations. This proves clause (1). Rationalize all lattices. On the qcqs final object,
sections commute with the filtered union of uniformly bounded denominator lattices in
internal Hom, computed on finite free charts. Hence sheaf Hom is the same bounded-
denominator colimit as equivariant linear Hom. A stable integral lattice in each continuous
finite-dimensional representation gives essential surjectivity. Applying the Hom formula
to the identity between any two lattices makes the rational action independent of the
lattice, proving clause (2). For clause (3), descend sheaves, maps, inverse maps and their
composite identities to a common finite coefficient field. Finitely many matrix entries
also descend equivariant linear maps, and injectivity of field inclusion tests their
intertwining equations. A representation already defined over a finite field comes from
clause (2). Finally tensor and scalar comparison maps are fixed on pure tensors.
Integral bases turn finite coefficient extension into a finite sum; cofinal uniformizer
filtrations let it commute with the integral limits. Rationalization and finite-field
descent give all remaining comparisons. Equality on pure tensors verifies their coherence.
Rank zero uses zero modules, and no invertibility of ell or separatedness is needed.
-/
theorem exists_normalized_coefficient_correspondences
    (ell : ℕ) [Fact ell.Prime]
    (X : Scheme.{u}) [ConnectedSpace X] [IsLocallyNoetherian X] [CompactSpace X]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (G : ProfiniteGrp.{u}) [∀ P, MulAction G ((Scheme.FiniteEtale.fiber x).obj P)]
    [CategoryTheory.PreGaloisCategory.IsFundamentalGroup (Scheme.FiniteEtale.fiber x) G]
    (c : Scheme.GaloisLisseFiniteCorrespondence x G) :
    ∃ C : Correspondences ell x G,
      (∀ E, IntegralNormalization ell x G c C E) ∧ Compatibilities ell x G C := by sorry

end AlgebraicGeometry.ProEtale.LisseRepresentation
