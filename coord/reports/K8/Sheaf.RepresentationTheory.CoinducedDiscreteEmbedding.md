## What changed

Proved `Rep.exists_coinduced_discrete_embedding` with the original statement.
Private constructions give the right-translation representation on `LocallyConstant`,
its open stabilizers, the object and postcomposition functor, locally constant orbit
functions, and their equivariant linear embedding. The natural transformation is
verified pointwise; evaluation at one proves injectivity. All data are explicit.

The proof generalizes the existing integer-coefficient construction in
`Sheaf.RepresentationTheory.LocallyConstantCochainsAcyclicEmbedding`; importing that
large cohomological development is unnecessary. Mathlib `LocallyConstant.comapₗ` and
`LocallyConstant.mapₗ` supply the linear precomposition and postcomposition maps.
LeanFinder, Loogle, the prescribed grep service, and local library searches were run.
The direct proof follows all three original DAG steps; its updated node records
exactly the construction and the sole non-elementary dependency.

Replaced the public import of `Sheaf.CategoryTheory.DiscreteModulesAbelian` by
`WeilConjectures.RepresentationTheory.DiscreteContinuousRep` and
`Mathlib.Topology.Connected.TotallyDisconnected`. The statement only needs the
representation definition, not the abelian/enough-injectives theorem. The change
record is `coord/changes/K8-coinduced-discrete-embedding-imports.md`.

Validation: the complete item compiled without warnings in 5.1 seconds via lcompile.py.
Original sources of all three direct consumers are being checked against the new
imports; their unchanged copies are verification inputs only, not delivered changes.
The delivery tool additionally probes all declarations for forbidden axioms.

## Proved and sorry left

Closed 1 of 1 original holes: `Rep.exists_coinduced_discrete_embedding`
(node `lem-exc-coinduced-discrete-embedding`). Added 0 holes and split off 0 statements.
There are no remaining `sorry` declarations in the item or added by this delivery.
The open-stabilizer dependency `ProfiniteGrp.exists_openNormalSubgroup_right_invariant`
is already proved. The original theorem signature, including all universes and its
finite-ring hypothesis, is unchanged.

## No longer needed

Removed import: `Sheaf.CategoryTheory.DiscreteModulesAbelian`.
The node `lem-exc-discrete-modules-abelian` is no longer a proof dependency: only the
underlying category definition is used, so it remains a statement dependency.
Its abelian structure, injective embeddings, and exactness declarations are not used
by this proof. This removes this item's import edges to
`Sheaf.RepresentationTheory.DiscreteContinuousInjectives` and
`Sheaf.RepresentationTheory.DiscreteRep`; they remain needed by other consumers.
No global claim is made that these modules leave the targets' closure.
Retained `Sheaf.Topology.ContinuousOpenNormalStabilizer`, the required topological step.
No node or module is withdrawn. The unit route is unchanged; the associated unit's
realized statement/step lists do not prescribe another route for this auxiliary node.

## Where the brief, the DAG or earlier work was wrong

The abelian-category dependency was stronger than the construction needs. Its definition
is available independently in the upstream discrete representation module. No mathematical
statement error or definition repair was needed.

The right-translation and orbit calculations work for the trivial group, zero module,
and zero ring as well as nontrivial examples; the proof introduces no nonzero, nonempty,
faithfulness or finiteness hypothesis beyond the original signature. Compactness and
profinite separation are used only to obtain open stabilizers for function modules.
The construction itself does not need finiteness of A, although the original theorem
retains it. Data are never chosen from an unproved existence statement.

## Second reading by K8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
