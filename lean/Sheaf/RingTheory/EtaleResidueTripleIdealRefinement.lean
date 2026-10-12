/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleResidueTriples

/-!
# EtaleResidueTripleIdealRefinement

Source: Stacks Project, Algebra, Tags 04GN and 04GP.
(blueprint: lem-weil-pbc-etale-triple-ideal-refinement).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Algebra, Tags 04GN and 04GP.

Proof: Etaleness gives p B_q = q B_q (Stacks Tag 00U4, item (1)). Thus for f in q,
clearing denominators in membership of f/1 in p B_q gives g outside q with gf in pB.
Pass to the principal localization B_g. The map to K extends since g is outside q,
and its kernel and residue embedding give a compatible triple s over R, as in the
unit-refinement construction. Since g is invertible in B_g, the image of f belongs
to p B_g. The localization map is the required morphism of triples.
(blueprint: lem-weil-pbc-etale-triple-ideal-refinement). -/
theorem etaleResidueTriple_ideal_refinement
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K)
    (t : EtaleResidueTriples R p K χ) (f : t.B) (hf : f ∈ t.q.asIdeal) :
    ∃ (s : EtaleResidueTriples R p K χ) (a : t ⟶ s),
      ((etaleResidueTriplesRingDiagram R p K χ).map a).hom f ∈
        p.asIdeal.map s.α.hom := by sorry

end AlgebraicGeometry.Scheme
