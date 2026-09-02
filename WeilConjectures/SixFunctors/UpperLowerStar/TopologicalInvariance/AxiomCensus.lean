/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.UpperLowerStar.TopologicalInvariance

/-!

# Axiom census for the topological invariance of the small étale site and topos

Topological invariance of the small étale site ([Stacks 04DZ]) and of étale cohomology
([Stacks 03SI]) is unconditional. This file records `#print axioms` checks witnessing that;
they are run by the build, so a `sorry` reappearing anywhere in the transitive dependencies
of these declarations breaks compilation rather than going unnoticed.

Two checks suffice for the blueprint nodes
`lemma:weil-pbc-universal-homeomorphism-site-equivalence` and
`prop:weil-pbc-universal-homeomorphism-topos`:

* `AlgebraicGeometry.Scheme.Hom.isDenseSubsite_etale` dominates the site-level statements:
  its fields are discharged through `AlgebraicGeometry.Scheme.Hom.isEquivalence_etale`
  (hence also through `AlgebraicGeometry.Scheme.Hom.etaleEquivalence`) and through
  `AlgebraicGeometry.Scheme.Hom.functorPushforward_mem_smallEtaleTopology_iff`.
* `AlgebraicGeometry.Etale.cohomologyMap_bijective` dominates the sheaf-level statements: it
  goes through `AlgebraicGeometry.Etale.isEquivalence_upperStar` and hence through
  `AlgebraicGeometry.Etale.sheafEquivalence`, and
  `AlgebraicGeometry.Etale.cohomologyEquiv` is `AddEquiv.ofBijective` of it. Being stated
  for the coefficients `AddCommGrpCat.{u + 1}`, it also covers the instances discharging the
  coefficient hypotheses, which a census of a general-coefficient statement would not.

This file has no mathematical content; it is a leaf of the import graph.

## References

* [Stacks 04DZ], Étale Cohomology, Theorem 59.45.2.
* [Stacks 03SI], Étale Cohomology, Proposition 59.45.4.

-/

@[expose] public section

/--
info: 'AlgebraicGeometry.Scheme.Hom.isDenseSubsite_etale' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.isDenseSubsite_etale

/--
info: 'AlgebraicGeometry.Etale.cohomologyMap_bijective' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Etale.cohomologyMap_bijective
