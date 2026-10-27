## What changed

Completed `AlgebraicGeometry.Scheme.proEtaleCanonicalTensorPullback` by the
representative argument. The normalized algebraic inverse image and
`isKFlat_ringedToposPullback` preserve flat K-flat representatives. The published
signed-total isomorphism is natural by the proved summand naturality lemma.
Independent-coefficient K-flat resolutions and
`resolvingRepresentativesFullyFaithfulWhiskering` make restriction to representative
pairs fully faithful. Apply `tensorComparisonDescent` using the existing exact
pullback factorization, which is invertible on every complex. Its square gives
existence; proof irrelevance for membership witnesses gives uniqueness.

The complete combined file exceeded 60 seconds after optimization. Following the
brief's splitting rule, moved its existing tensor models and ordinary comparison
into `Sheaf.Paper.ProEtaleTensorPullbackModels`, publicly re-exported from the
item. The remaining combined proof was still over 60 seconds, so the proved
complex-level setup now lives in `Sheaf.Paper.ProEtaleTensorPullbackDescentData`.
The three final modules compiled in 25.9, 26.3 and 28.2 seconds respectively.
Every existing public declaration name, elaborated type, attribute and
definitional body is unchanged, as are all former public imports. Proved wrappers
preserve the private helper names used by import-all consumers. The private
normalized algebraic lift is a definitionally identical alias. Local
irreducibility and proved private helpers control unfolding in the new proof.
No source-library module is edited. Definition ownership records
`def-sfb-proetale-tensor-model` and
`def-sp-proetale-ordinary-tensor-pullback-total` point to the supporting module.
The shared theorem node retains its generic proof steps and adds the specialized
route. No mathematical statement, notion or unit route changes.

Compatibility: the public declarations and their bodies were compared with the
original prefix, allowing only the relocation and renamed private helpers. The
main theorem signature and canonical choice definition are unchanged. The
private-helper consumers `CompletedPullbackTensorComparison` and
`TensorCompletionChainUniqueness` compiled in 59.9 and 31.1 seconds. Direct
consumer checking encountered no signature or missing-declaration error, but
several files exceeded the time limit. Published-only baselines also timed out
for `CartesianCoefficientTwists`,
`RingedTopoiCanonicalTensorPullbackOfUniverses`,
`ProEtaleProjectionFormulaArrows` and `WeilTensorProduct`. A contemporaneous
profiled published-only `OpenImmersionTensorPiece` took 62.4 seconds and was
rejected, while the profiled changed-dependency version was accepted. The last
isolated checks accepted `IntegralCompactSupportCoefficientComparison` (54.6 s)
and `RingedProjectionGlobalModel` (42.6 s), while `PbcActualScalarPullback`
(67.0 s) and `ProEtaleRestrictedTensorFiniteLocalConstancy` (63.8 s) exceeded
the limit. These consumer time-limit failures remain a validation limitation;
their sources are not adapted or included in the delivery. The delivered files
themselves each pass the 60-second limit; the latest whole-packet probe also
accepted the descent-data and item modules at 44.2 and 45.2 seconds.

Change record: `coord/changes/E4-proetale-tensor-pullback-module-split.md`.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.Scheme.proEtaleCanonicalTensorPullback`
(node `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`).
Zero holes remain in all three delivered Lean modules. Zero holes added, zero split off.
The new `AlgebraicGeometry.Scheme.proEtaleTensorPullbackDescentData` theorem
is completely proved from existing declarations.
This is a proof from existing declarations, not a decomposition.

## No longer needed

No module is withdrawn or globally pruned. These proof imports moved from the
item to its supporting model module because only the ordinary construction uses
them: `CochainTensorUniverses`,
`RingedTopoiCanonicalTensorComparisonOfUniverses`, and
`ProEtaleCanonicalAdjunctionUnit`. They remain necessary there.

The pro-etale specialization does not need
`derivedPullback_kflat_tensor_computation`
(`lem-weil-pbc-kflat-tensor-pullback-computation-universes`),
`ringedTopoiDerivedPullback` (`lem-weil-pbc-ringed-topoi-derived-pullback`), or
`kFlat_total_tensor_model` (`lem-pur-kflat-total-tensor-model`) to establish
comparison invertibility: `proEtaleRingDerivedPullbackFactors` is an isomorphism
on all complexes, including total tensors. The shared node also describes the
general ringed-topos theorem, whose proof still uses those dependencies, so they
remain in that node and are not globally pruned.
The general theorem in `RingedTopoiCanonicalTensorPullbackOfUniverses` cannot be
imported here: it already publicly imports the item, which would create a cycle.

## Where the brief, the DAG or earlier work was wrong

The shared theorem node records both the general ringed-topos interface and this
pro-etale specialization. The general computation step is unnecessary in the
specialization because identified-coefficient pullback is exact. The unit route
is preserved: the representative tensor square, flat K-flat preservation and
uniqueness are all proved without changing any statement or notion.

Mathlib search: LeanFinder returned ordinary flat module tensor results, without
a representative-descent match; Loogle returned no hit for the submitted
whiskering query; grep returned no Mathlib match. Project searches found the
already proved `tensorComparisonDescent` and resolving-representative
restriction lemmas, which are used directly. The argument follows Stacks
`sites-cohomology.tex`, `lemma-pullback-tensor-product` (07A4), and
`sites-modules.tex`, `lemma-tensor-product-pullback` (03EL), read in the supplied
literature. Empty schemes, zero coefficients and unbounded complexes require no
extra hypothesis. Arbitrary supplied tensor models are handled by their given
representative isomorphisms and fully faithful restriction.

## New nodes

`lem-weil-pbc-proetale-tensor-descent-data`, realized by
`Sheaf.Paper.ProEtaleTensorPullbackDescentData`, records the proved complex-level
setup: preservation of the representative class, full faithfulness of restriction,
and naturality of the ordinary total comparison with its prescribed components.
It asserts no derived tensor comparison and is strictly the setup part of the
argument; the item constructs the derived comparison and proves its stipulated
square and uniqueness by descent. This node has no holes. Its three searches
found generic totalization/localization tools but no combined specialized theorem.
Change record: `coord/changes/E4-proetale-tensor-pullback-module-split.md`.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
