/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.Paper.LisseQlbarRepresentationDefs
import Sheaf.Paper.GaloisLisseRepresentations
import Sheaf.Paper.CoefficientFiniteDescentLisse
import Sheaf.Paper.NormalizedLisseCoefficientCorrespondences
import Sheaf.Paper.LisseGeometricFibresFiniteFree
import Sheaf.Paper.NormalLisseFiniteCoefficientLattice
import Sheaf.RepresentationTheory.ContinuousAlgClFiniteModel

/-! # Lisse condensed coefficients and continuous representations

Source: blueprint latest, thm-lisse-qlbar-representations, clauses (1)--(5).
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

/-- Lisse condensed coefficients and continuous representations, with the finite-level
normalization, actual geometric fibres, and canonical tensor/scalar comparisons.
Source: blueprint latest, sec-six-functors/sk-lem-finite,
`thm-lisse-qlbar-representations`, clauses (1)--(5)
(blueprint: thm-lisse-qlbar-representations).

Proof: take the finite Galois correspondence and construct its normalized simultaneous
integral, rational and algebraic-closure correspondences. Independently compute finite
free geometric fibres for the three coefficient types. On a normal X, the finite-
coefficient lattice theorem supplies lattices; finite coefficient descent then supplies
integral finite-field models for every lisse algebraic-closure module. For representations,
choose a finite basis, descend the continuous matrix action to a finite p-adic field by
compact matrix descent, and use its invariant coordinate subspace and canonical tensor
comparison. This proves the field-of-definition clause. Finally the existing
regular-scheme theorem makes every stalk an integrally closed domain. These independent
arguments give all nine conjuncts of Conclusion with exactly the specified fibres.
-/
theorem lisse_qlbar_representations (ell : ℕ) [Fact ell.Prime]
    (X : Scheme.{u}) [ConnectedSpace X] [IsLocallyNoetherian X] [CompactSpace X]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (G : ProfiniteGrp.{u}) [∀ P, MulAction G ((Scheme.FiniteEtale.fiber x).obj P)]
    [CategoryTheory.PreGaloisCategory.IsFundamentalGroup (Scheme.FiniteEtale.fiber x) G] :
    ∃ (c : Scheme.GaloisLisseFiniteCorrespondence x G) (C : Correspondences ell x G),
      Conclusion ell x G c C := by
  obtain ⟨c, _⟩ := Scheme.galois_lisse_representations x G
  obtain ⟨C, hnorm, hcompat⟩ :=
    exists_normalized_coefficient_correspondences ell X x G c
  obtain ⟨hfreeInt, hfreeRat, hfreeAlg⟩ := lisse_geometric_fibres_finite_free ell x
  refine ⟨c, C, hnorm, hcompat, hfreeInt, hfreeRat, hfreeAlg, ?_, ?_, ?_, ?_⟩
  · exact fun hn E L hL ↦ has_lattice_of_normal ell X hn E L hL
  · intro hn L hL
    obtain ⟨E, M, hM, e⟩ := (coefficient_finite_descent_lisse X ell).1 L hL
    exact ⟨hL, E, M, ⟨hM, has_lattice_of_normal ell X hn E M hM⟩, e⟩
  · intro V hV
    let : FiniteDimensional (PadicAlgCl ell) V.V := hV.1
    exact Representation.isLAdic_of_continuous_dual_coefficients ell G V.V
      (linearAction V) hV.2
  · intro hreg z
    let : IsRegular X := hreg.2
    exact ⟨inferInstance, IsRegular.isIntegrallyClosed_stalk z⟩

end AlgebraicGeometry.ProEtale.LisseRepresentation
