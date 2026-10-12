/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# EtaleResidueTriplesRepresentatives

Source: Stacks Project, Algebra, Tags 04GN and 04GP.
(blueprint: lem-weil-pbc-etale-triples-colimit-representative).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Algebra, Tags 04GN and 04GP.

Proof: The category of pointed etale algebras is filtered by
etaleResidueTriples_filtered_part, for arbitrary K and chi. Inside c.pt let S be
the elements represented by some coprojection. The identity triple represents zero
and one. Negatives stay represented at the same triple. For addition and multiplication,
filteredness supplies a common successor of the two representing triples; cocone
naturality represents the result there. Thus S is a subring of c.pt.
Every coprojection restricts to S, defining a cocone cS. The colimit universal
property gives d : c.pt -> S. The inclusion i : S -> c.pt satisfies i composed with d
= identity: both maps agree on every coprojection, so colimit uniqueness identifies
them. For any x, d(x) is in S and i(d(x))=x, hence x is represented. This argument
uses no small skeleton or preservation theorem for an underlying-set functor.
(blueprint: lem-weil-pbc-etale-triples-colimit-representative). -/
theorem etaleResidueTriples_colimit_representative
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K)
    (c : Cocone (etaleResidueTriplesRingDiagram R p K χ)) (hc : IsColimit c)
    (x : c.pt) : ∃ (t : EtaleResidueTriples R p K χ) (f : t.B),
      (c.ι.app t).hom f = x := by sorry

end AlgebraicGeometry.Scheme
