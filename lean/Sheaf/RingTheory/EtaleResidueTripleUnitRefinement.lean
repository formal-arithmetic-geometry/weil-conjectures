/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleResidueTriples

/-!
# EtaleResidueTripleUnitRefinement

Source: Stacks Project, Algebra, Tags 04GN and 04GP.
(blueprint: lem-weil-pbc-etale-triple-unit-refinement).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Algebra, Tags 04GN and 04GP.

Proof: For an element f outside the prime q of a triple, form the principal localization B_f.
The map B → K extends to B_f because the image of f in K is nonzero and hence a unit.
Let q' be the kernel of this extension and extend the resulting injection B_f/q' → K
to its fraction field. This gives the residue-field embedding of the new triple.
The extended map agrees on R, so q' lies over p and the triple is compatible with χ.
Principal localization is etale, and composition with the given etale map is etale.
The localization map is a morphism of triples and takes f to a unit.
(blueprint: lem-weil-pbc-etale-triple-unit-refinement). -/
theorem etaleResidueTriple_unit_refinement
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K)
    (t : EtaleResidueTriples R p K χ) (f : t.B) (hf : f ∉ t.q.asIdeal) :
    ∃ (s : EtaleResidueTriples R p K χ) (a : t ⟶ s),
      IsUnit (((etaleResidueTriplesRingDiagram R p K χ).map a).hom f) := by sorry

end AlgebraicGeometry.Scheme
