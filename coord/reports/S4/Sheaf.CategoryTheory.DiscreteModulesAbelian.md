## What changed

Proved CategoryTheory.discreteModules_abelian in
Sheaf.CategoryTheory.DiscreteModulesAbelian. Rep.discreteRep_abelian_structure supplies
the abelian structure, additivity, finite-limit/colimit preservation and exactness.
Mathlib gives enough injectives for the small lifted group ring; the proved group-ring
equivalence and ModuleCat.openStabilizerAdjunction transfer them to discrete actions.

Corrected the false independent-carrier-universe encoding to carrier max u w.
Generalized the explicit construction in the unclaimed module
Sheaf.RepresentationTheory.RepresentationLiftedGroupAlgebraEquivalence to independent
carrier and coefficient-lift universes, proving
Rep.representation_liftedGroupAlgebra_equivalence_anyUniverse. The old public equivalence
keeps its exact signature and is a specialization. No new definition contains a hole.
Change record: coord/changes/S4-discrete-modules-abelian-universes.md.
Updated both existing DAG nodes to match the actual route.

## Proved and sorry left

The original declaration CategoryTheory.discreteModules_abelian had one hole, but its
independent-small-universe statement was false. The delivery replaces it with a fully
proved corrected universe statement, not a proof of that false stronger statement.
No holes remain in the item; zero holes added or split off. The equivalence generalization
and its original specialization are also fully proved. The axiom prints for the corrected
theorem and the new equivalence contain only propext, Classical.choice and Quot.sound.

Compiled the two changed modules and, unchanged, DiscreteContinuousFunctorialInjectives,
ContinuousCochainsDeltaFunctor, ContinuousCochainsInvariantsZero,
ContinuousCochainsDerivedInvariants and DiscreteContinuousCohomology. The unchanged
consumer modules have their own pre-existing holes and are not part of the delivery.

## No longer needed

Removed proof import Sheaf.RepresentationTheory.DiscreteContinuousInjectives and dependency
lem-exc-discrete-modules-abelian-injective-embeddings: the small-ring Mathlib theorem and
the open-stabilizer adjunction supply enough injectives directly, without a functorial
embedding endofunctor. This route also avoids needing the functorial embedding chain
Sheaf.RepresentationTheory.DiscreteContinuousFunctorialInjectives,
Sheaf.GroupTheory.GroupAlgebraFunctorialInjectiveEmbeddings and
Sheaf.CategoryTheory.AdjunctionTransferFunctorialInjectives, including nodes
lem-exc-rg-discrete-modules-functorial-injective-embeddings,
lem-exc-rg-group-algebra-functorial-injective-embeddings and
lem-exc-rg-adjoint-transfer-functorial-injectives, for this item. These may remain needed
by other items; no module is withdrawn. No unit realization is bypassed: sk-prop-h2's
realized statement and steps lists are empty. All retained imports support the statement
or the actual proof.

## Where the brief, the DAG or earlier work was wrong

The previous statement asserted enough injectives in an independent carrier universe
that may be smaller than G. This is false; the coordinate-character counterexample is
in the change record and was already identified by the G3 repair of its embedding
lemma. The repaired statement uses a universe containing G; finiteness of A removes
any need to enlarge further to v. Every existing application already uses this carrier,
so no consumer or target statement changes. The original group-ring equivalence had an
unnecessary shared universe bound on its construction, now generalized with a proof.
The retained attempt had no report or change record; these are now supplied.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
