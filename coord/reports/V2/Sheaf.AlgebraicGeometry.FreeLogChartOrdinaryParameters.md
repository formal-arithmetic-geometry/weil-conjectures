## What changed

Replaced the sorry in `AlgebraicGeometry.freeLogChart_ordinary_parameters` by a complete Lean
assembly from three strictly smaller statements. The assembly specializes the generic
specified-list descent lemma using `List.map_map`, derives regularity of every ordinary stalk
from a parameter list using the spanFinrank bound, and constructs geometric points from
algebraic closures of the residue fields. It proves that the characteristic is subsingleton
exactly when all coordinates are units: a nonunit index would distinguish the constant-zero
and constant-one exponent vectors. Mapping finite products and `Scheme.mem_basicOpen_top`
then prove the locus equality and the unit assertion. The r=0 assertion is an empty product.
The original theorem signature is byte-for-byte unchanged. Its existing quantified proof
binder `ht` does not occur later in the conclusion; a local unused-variable lint setting
preserves that signature without a style warning. No proof or kernel check is disabled.

Moved `FreeLogChart.coordinate`, `ordinaryCoordinate`, `strictCoordinate`, and `nonunitIndices`
unchanged to `Sheaf.AlgebraicGeometry.FreeLogChartCoordinates`, which the item publicly imports.
This avoids a circular import in the new strict-local statement. A text comparison verified
identical definition bodies and signatures; only their blueprint ownership tags changed.
Change record: `coord/changes/V2-free-log-chart-coordinate-ownership.md`.
There are no existing direct Lean importers or external declaration users to adapt.

The source was checked in ILO VI 1.1--1.2 and 1.6--1.7, printed pp. 69--70, and Stacks
more-algebra.tex Tag 06LN (including its minimal-generator proof), Tag 07QM, and algebra.tex
Tag 00KU. The unit's statement and proof steps are preserved; only this node's local argument
is factored. New statements include empty prefixes, zero-dimensional rings, and r=0; the
main stalkwise proof is vacuous on an empty scheme.

Remote single-file compiles checked all five modules; compilation of the item took 5.2 s
before the final lint cleanup. The required delivery pipeline validates the final packet.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.freeLogChart_ordinary_parameters`
(node `lem-trf-free-log-chart-ordinary-parameters`). There are zero sorries in the item module.
Its private `regular_of_parameters` helper is completely proved from Mathlib.

Added three holes, each in a new module with source and full proof in words:

- `AlgebraicGeometry.etale_logRegular_restriction`
  (`lem-trf-etale-log-regular-restriction`): only restriction, log regularity and locus transport;
  no free chart or parameter conclusions.
- `AlgebraicGeometry.freeLogChart_strict_parameters`
  (`lem-trf-free-log-chart-strict-parameters`): the free-chart presentation and parameters at
  one strict-local ring; no ordinary parameter descent, scheme regularity or locus assertion.
- `AlgebraicGeometry.strictLocal_parameters_descent`
  (`lem-trf-strict-local-parameter-descent`): generic descent for an arbitrary specified list
  of global functions, conditional on its strict-local parameter extension; no log structure.

This is a decomposition: one upper hole closed, three lower holes added, net -2 holes.
It is not a complete proof from the standard axioms. No new definition contains a hole,
and no data is chosen from a new existence theorem. The characteristic equivalence is only
eliminated inside a proof. All four moved definitions remain explicit constructions.

## No longer needed

Removed these original proof-only imports from the item:

- `Sheaf.AlgebraicGeometry.IndEtaleStrictLocalInvariance`
- `Sheaf.RingTheory.IndEtaleUniverseTransport`
- `Sheaf.AlgebraicGeometry.AffineStrictLocalRingComparison`
- `WeilConjectures.RingTheory.StrictHenselizationNoetherian`
- `WeilConjectures.RingTheory.StrictHenselizationFaithfullyFlat`
- `WeilConjectures.RingTheory.StrictHenselizationRegular`
- `WeilConjectures.RingTheory.StrictHenselizationCotangentDimension`
- `Mathlib.RingTheory.Localization.Submodule`
- `Mathlib.RingTheory.LocalRing.Module`

The first two modules and the nodes `lem-trf-ind-etale-strict-local-invariance` and
`def-weil-pbc-ind-etale-algebra` are unnecessary for this route. The new restriction step
uses the pointed-etale slice directly, rather than the much stronger general ind-etale
invariance theorem with arbitrary base change and a structural-map clause.
This does not assert that those nodes have no other consumers.

The affine comparison, strict-henselization results, cotangent dimension, local Noetherian
localization, and Nakayama results remain mathematical dependencies of the corresponding
new lower statements, whose nodes name them. They are not claimed pruned; they simply
are no longer direct proof imports of the item. The regular-scheme, parameter and basic-open
definition/Mathlib leaf nodes remain used. Every new proof-only import in the item is used.
The parent node's five former direct `tool_uses` approvals are withdrawn there, because
these dependencies now occur in the new strict-local and descent nodes: affine strict-local
comparison, strict-henselization Noetherianity, faithful flatness, regularity and cotangent
dimension. No new tool approval is added; their retained mathematical uses are recorded
explicitly in the lower nodes.

No existing module or declaration is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original step 3 was labelled elementary, but its explicit free-chart pushout and ideal
calculation is substantial Lean work not supplied by its sole definition dependency.
Steps 5--6 also require preserving a prescribed initial list, which the regularity and
cotangent-dimension declarations alone do not directly state. The new nodes expose those
missing interfaces rather than changing the statement or choosing unrelated parameters.
The stronger ind-etale step can be replaced by ordinary pointed-etale slice cofinality.
No mathematical counterexample or target-statement correction was needed.
The delivery checker reports a statement-change advisory solely because `stmt_deps`
now names the relocated coordinate definition node. Both the natural-language statement
and Lean signature remain unchanged; the dependency/ownership change is documented in
the change record. No fictitious statement correction was added to silence that advisory.
The first preflight's only enforced failure was that the coordinate attachment included
the `noncomputable` modifier, while the checker records signatures starting at `def`;
this metadata has been corrected. LeanSearch provenance was added for every new node.

## New nodes

`def-trf-free-log-chart-coordinates` owns the four real coordinate/list constructions,
relocated without changing their bodies or qualified names.

`lem-trf-etale-log-regular-restriction` is the etale restriction part of original step 1.
It has no chart hypothesis and no regular-parameter conclusions.

`lem-trf-free-log-chart-strict-parameters` is original steps 2--4 at a single geometric
point, retaining the normalized monomial map and the actual indexed coordinate values.

`lem-trf-strict-local-parameter-descent` is the prescribed-prefix consequence of original
steps 5--6, for any finite list of global functions on any locally Noetherian scheme.
Its strict-local hypothesis is supplied by the preceding node; the Lean assembly performs
that specialization and independently derives scheme regularity and the basic-open locus.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
