## What changed

Replaced the body of `realizationIntegralReindex_scalar` by a categorical assembly
of two independent scalar squares. Its statement and public imports are unchanged.
The proof factors the specified integral comparison, moves the completion map by
naturality, applies the ambient balancing square, uses `S.common_field`, and then
uses the specified rational component and a generic equality-transport lemma to
remove the explicit endpoint transport.

Added `AdicReindexScalarData` with concrete scalar/reindexing maps. The two completed
coefficient transports agree by their finite projections; their exact derived
functors are identified by equality transport. The exact scalar model is selected
from an existing unique normalized existence theorem, not arbitrary existence.
The scalar/reindexing map is a composite of these identifications with the existing
section-normalized `isomorphismScalarTensorDerived`.

Added `AdicReindexScalarSource`, which constructs the source factors of the integral
comparison independently of S, B and I, and states their scalar square. Added
`AdicReindexBalancedScalar`, which states the independent square of ambient ordinary
derived scalar tensors. Both are private proof imports of the assigned module.
No existing foreign module or target statement is changed. Associativity, naturality,
and endpoint transport are proved first in generic categories and then specialized;
no category-instance attributes are changed.

Validation: the final `lcompile.py --all` run compiled all four delivered modules
without warnings. Times were 15.9 s (data), 21.9 s (ambient balancing), 29.4 s
(source), and 42.0 s (assigned module), all below 60 s. Profiling options are removed.
The original theorem signature was also checked byte-for-byte against the source.

## Proved and sorry left

This is a decomposition, not a net proof: one original hole is replaced by two
strictly smaller holes. The assigned module has zero remaining `sorry`.

Original hole closed by the assembly:
`WeilConjectures.AdicQbarRealization.realizationIntegralReindex_scalar`
(`lem-sf-adic-realization-reindex-scalar`).

Holes added, one whole named public theorem per new module:

- `WeilConjectures.AdicQbarRealization.realizationReindexSource_scalar`
  (`lem-sf-adic-reindex-scalar-source`). This contains only the source realization R,
  its common-field normalization, and the completed-to-tower scalar comparison.
  It has no S, B, I, native balanced inverse-image square, or rational comparison c.
- `WeilConjectures.AdicQbarRealization.integralReindex_balanced_scalar`
  (`lem-sf-adic-reindex-balanced-scalar`). This is an ambient ordinary derived tensor
  square: it has no common stage, realization integral comparison, constructibility,
  invertibility-of-l hypothesis, or completion map. The independent normalization
  conditions on IE and IL fix its two maps.

The new coefficient-map equality, exact inverse-image model, literal stage-object
identity, canonical scalar arrow, generic source-composite component formula, and
source comparison construction have complete proofs or concrete bodies. The assigned module's factorization, common-field
transport, and assembly proofs have no admitted steps. The concrete source comparison
is expressed through a generic source composite with a proved component and
factorization API, avoiding repeated normalization of large derived functor terms.
No data definition contains a hole. Neither new theorem is the original conclusion with repackaged hypotheses:
the original follows by their nontrivial naturality and cancellation calculation.
The source square and ambient square can be proved independently.

Both new statements were checked on identity coefficient embeddings, zero objects,
empty schemes, and ramified finite extensions. The ambient square uses ordinary
scalar extension, so it neither assumes completeness nor inverts a completion unit.
The source square only inverts the already-proved constructible comparison.

## No longer needed

No original public import is removed, no module is withdrawn, and no mathematical
dependency is claimed globally pruned. The data helper's native import is
`NativeAdicFiniteNormalization`; it also imports the existing normalized scalar model.
`NativeAdicReindexingData` is imported directly by the balancing statement, which
needs its interface. The original direct proof dependencies for
whole-cone normalization, finite-free completion, and scalar inverse image now belong
to the smaller source square; the representative and pure-tensor calculations belong
to the ambient square. The assigned node records its actual new direct dependencies.
No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement was found false. The original plan combines two scalar compatibilities
that its declared interfaces do not state directly. In particular,
`isomorphismComparison_scalarExtension` concerns a specified completed inverse-image
comparison, whereas the source factor here uses the separately constructed
`podCompletedToTower`; their whole-cone normalization must be identified. Also, the
representative equations of IE and IL identify their own derived maps but do not
state the coefficient-enlargement associativity square. The two new statements
isolate these separate calculations without restating the full realization square.

The library search also found `continuousMixedOrdinaryBalance`, but it is expressed
in the bounded `ContinuousRational.Base`, `At`, `Along`, and `AmbientMixed` interfaces.
Those are not the arbitrary-scheme native data of this item, so that statement does
not directly instantiate to the required square.

The scalar maps are constructed before the two statements are stated, so the smaller
obligations cannot choose maps to make their conclusions true. The newest blueprint
unit route and existing source-library declarations are preserved.

## New nodes

`def-sf-adic-reindex-scalar-maps` records the concrete ordinary derived scalar/reindexing
comparison and the native scalar transition. Its module has no holes and chooses
only from the existing uniquely normalized scalar-model theorem.

`lem-sf-adic-reindex-scalar-source` records the actual source comparison, its literal
stage endpoint, and its scalar square. It isolates completion and common-stage
source compatibility from all target balancing data.

`lem-sf-adic-reindex-balanced-scalar` records the independent ambient balanced-tensor
square, normalized by the section and representative equations. This is the pure
tensor part of Step 3 of the original plan, before completion or localization.

Change record: `coord/changes/G8-adic-reindex-scalar-maps.md`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 INFRA.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.AdicRealizationReindexScalar": "824091932123baf2598235b8bd87fedc83b092e1", "Sheaf.Paper.AdicReindexBalancedScalar": "f238905f89f3a6e06b033b8015c69f792f66246f", "Sheaf.Paper.AdicReindexScalarData": "02fb735fc3094df612c568e400bcd40294eff145", "Sheaf.Paper.AdicReindexScalarSource": "31011f4e1f1d6fcac51db5b8c166a1430f55869a"}, "results": {"Sheaf.Paper.AdicRealizationComparisonDescent": {"hash": "9898dcf3ae87550c93b1c1c749b7db0a36562903", "status": "INFRA"}}, "seconds": 75, "time": "2026-10-28T12:39:54+0800", "transitive": 0, "version": 1}
```

## Second reading by G8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
