/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-!
# Directed colimits of derived etale cohomology at coefficient size

Source: Stacks Project, Tag 03Q5 (lemma-colimit).
(blueprint: lem-weil-pbc-etale-directed-cohomology-colimit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Derived etale cohomology preserves directed colimit cocones indexed in the
same universe as the abelian coefficients.
Source: Stacks Project, Tag 03Q5 (lemma-colimit), direct proof, and
Tag 0739 (lemma-colim-works-over-collection), proof.
(blueprint: lem-weil-pbc-etale-directed-cohomology-colimit)

Proof: Work simultaneously on all qcqs etale objects. Every etale cover of one
of these objects has a finite qcqs refinement whose finite fibre products are
qcqs. Sections of a directed colimit commute with evaluation on these objects:
choose representatives on the finite cover and move their finitely many matching
equalities to one upper stage. This proves the degree-zero comparison.
Embed the sheaf diagram functorially into injectives and take its cokernel
diagram. Exactness of filtered colimits gives the corresponding short exact
sequence after colimiting. For every finite qcqs cover, sections commute with
colimits, and finite products do too, so the Cech complex of the colimit of
injectives is the colimit of their Cech complexes. Their augmented complexes
are exact. Exactness of filtered abelian-group colimits therefore gives Cech
vanishing for the colimit of injectives. The Cech vanishing criterion on the
qcqs basis makes that colimit acyclic. Compare the natural long exact sequences
of the stagewise short exact sequences and of their colimit. Degree one is the
cokernel of the same map of degree-zero sections. In degree greater than one,
acyclicity identifies the comparison with the preceding-degree comparison for
the cokernel diagram. Induction simultaneously for all diagrams proves every
degree. Injective resolutions identify this cohomology naturally with the
homology of derived global sections, sending every coprojection to the displayed
functor's map. Thus the image cocone is a colimit. Only finite upper bounds are
used, so an index in universe u+1 is allowed. Identity diagrams and zero sheaves
give identity and zero colimit cocones; no torsion hypothesis is required. -/
theorem etaleCohomology_isColimit_of_isDirected (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] {I : Type (u + 1)} [PartialOrder I]
    [IsDirected I (· ≤ ·)] [Nonempty I]
    {D : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {c : Cocone D}
    (hc : IsColimit c) (q : ℕ) :
    Nonempty (IsColimit
      ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
        Etale.cohomology AddCommGrpCat.{u + 1} X (q : ℤ)).mapCocone c)) := by
  sorry

end AlgebraicGeometry.Scheme
