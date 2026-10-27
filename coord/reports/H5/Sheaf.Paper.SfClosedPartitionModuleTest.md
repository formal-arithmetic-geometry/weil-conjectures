## What changed

Replaced the proof of `AlgebraicGeometry.Scheme.sf_closed_partition_module_test`
in `Sheaf.Paper.SfClosedPartitionModuleTest`. The statement and existing public
interface are unchanged. The proof follows the three existing DAG steps:

1. Apply `noetherian_complementary_stratifications`, upgrade its finite locally
   closed partition using its constructibility clause, and retain its exact
   dependent-pair equalities. The index equivalence proves positivity by comparing
   finite cardinalities. Compactness of all subsets gives retrocompactness directly.
2. Use `sfClosedPartitionRestrictionIso` for each old stratum, applying the existing
   canonical module pullback compositor and the supplied identification.
3. Transport local trivializations using the restriction functor on localized sites,
   and transport finite stalks using `geometricRingModuleStalkFunctor.mapIso`.
   The constant zero presheaf has zero identity, so its sheafification is zero.
   The same proof works on a localized site. An identity cover therefore trivializes
   the open zero restriction, and the additive stalk functor sends it to a zero module,
   whose underlying type is subsingleton and finite. Fin.lastCases, after rewriting
   the dependent-pair equality, verifies these properties on the chosen partition.

The module compiles cleanly through `lcompile.py`.
All added helpers are private and proved. No new modules or imports are required.
The argument permits an empty original partition, empty strata, empty ambient,
closed or open schemes, and the zero coefficient ring; it never replaces a scheme
by its reduction. The existing geometry dependency still contains its own sorry;
this is the intended stage-3 proof from previously stated dependencies.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.Scheme.sf_closed_partition_module_test`
(node `lem-sf-closed-partition-module-test`).
Added zero holes. There are zero sorries left in the delivered module.
No statements are split off.

## No longer needed

None. The proof retains the reviewed geometry and canonical pullback-composition
route, as well as the local-constancy, stalk and constructibility definitions.
No imports, nodes or modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was necessary. The supplied constructibility hypothesis
`hS` is redundant because the geometry dependency already supplies constructibility
of the ambient partition. It is retained verbatim. At the common universe, the two
local-constancy encodings identify by unfolding their cover-and-model definitions.
Restriction to a localized ringed site has no registered zero-preservation instance;
the proof checks its zero identity componentwise instead.

## Second reading by H5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
