## What changed

Repaired and proved `section_pull_transport_condition_of_normalized` in
`Sheaf.Paper.QuotientSectionPullTransport`. It now explicitly requires the two
`ScalarSectionNormalized` hypotheses that fix the endpoint derived isomorphisms.
The only caller, `section_pull_transport`, already has these hypotheses and passes
them through; its signature and the unit route are unchanged. The proved helper `section_pull_transport_condition_on_computed` in the new module
`Sheaf.Paper.QuotientSectionPullTransportComputed` pastes the scalar, geometric, ordinary and normalized computation squares, cancels
invertible computation maps on K-flat representatives, and transports the equality
to arbitrary derived objects by naturality. No coefficient flatness assumption is
introduced. The argument also covers empty schemes and zero coefficient rings:
it never assumes a point, a nonzero object, or a nontrivial scalar.

The geometric computation helper imports `Sheaf.Paper.SectionDerivedPushpullNormalization` for the existing
geometric computation equations. The item imports
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalIso` for the proved
`CondensedRing.exists_kFlat_iso_Qh_obj` representative lemma. It uses the source's
scoped `CachedModInstances` to share the standard module-object instances. Its generic categorical pasting helpers were
adapted from the proved private helpers in `SectionPullComputationOfRealization`;
that module is not imported. The existing normalized-comparison existence proof
from the current source is retained, and its DAG dependency record is synchronized
with its K-flat construction and extension lemmas.

Validation: all four delivered proof files compile (15.2 s, 14.9 s, 38.6 s, and
8.7 s). The unchanged direct importer
`Sheaf.Paper.QuotientSectionTensorNormalization` also compiles (5.1 s); its test
copy is excluded from the delivery.

Change record: `coord/changes/H1-quotient-section-pull-normalization.md`.

## Proved and sorry left

The current source has one hole, in
`AlgebraicGeometry.ProEtale.QuotientSectionTensor.section_pull_transport_condition_of_normalized`.
Its corrected, explicitly normalized statement has a complete proof. The original
unconditional statement was false, so this delivery does not claim to prove it.
The final `section_pull_transport` remains proved with exactly its original
signature. The already proved `section_pull_transport_section_normalized` is retained.
There are zero holes left in the item and zero new holes or split-off obligations.
The new public helpers `section_pull_transport_scalar_computation`,
`section_pull_transport_geometric_computation`, and
`section_pull_transport_condition_on_computed` are also proved completely; this is a split into
proved files for compilation time, not a decomposition into open obligations.
The imported existing K-flat existence and extension obligations remain unchanged.

## No longer needed

The compatibility proof does not depend on the existence lemma
`lem-sfb-quotient-section-pull-transport-section-normalized`: it uses its supplied
normalized witness directly. This obsolete edge is removed from the compatibility
node. The final transport theorem still uses the existence lemma, its K-flat
construction, and its extension lemma, so none of those modules is pruned.
The old direct proof import `Sheaf.Paper.IntegralResidueDerivedMonoidal` and its
file-local projection-instance registrations are unnecessary for this argument.
The imported K-flat existence and extension modules retain their own dependencies,
so removing this direct import does not withdraw the derived-monoidal node or module.
Unused copied private helpers for cochain counits and cochain equivalences were
removed. No unit step is bypassed. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (original compatibility statement): `SectionPullNormalized`
constrains the ordinary comparisons and model counits, while `PullSectionCondition`
also uses `cX.derived` and `cY.derived`. Without endpoint normalization these are
arbitrary isomorphisms. For identity maps and integral coefficients on a nonempty
scheme, negating one endpoint derived isomorphism preserves the old hypotheses
and changes the required identity by a sign. The source normalization equations
supply precisely the missing constraints. The parent theorem already assumes
them; no target or definition changes.

The queue's old hole count was two, whereas the current source had one: its
existence lemma was already proved using the K-flat and extension modules. Its DAG
proof-dependency record had not yet reflected those imports. The delivery preserves
that proof and records its actual dependencies. The geometric computation theorem
is used as a general tool; it does not replace any unit route.

## New nodes

`lem-sfb-quotient-section-pull-transport-computed` records the proved computation
at a cochain representative with invertible scalar counit. It is strictly the
representative step: the parent still chooses a K-flat representative, obtains
invertibility of its counit, and transports the equality to an arbitrary derived
object by naturality. The new module contains this one public theorem and proved
private categorical helpers. Splitting it off keeps both files below the per-file
compile limit after sharing the standard source instances. No shared definition
is changed. The endpoint statement repair is recorded in
`coord/changes/H1-quotient-section-pull-normalization.md`.

`lem-sfb-quotient-section-pull-transport-scalar-computation` records the endpoint
scalar equation with the universal counit and canonical cochain comparison. Its
proof extracts the all-complex clause of the supplied normalization and identifies
the computation map with the scalar counit. It is proved, with no hole.

`lem-sfb-quotient-section-pull-transport-geometric-computation` records the geometric
computation square using the canonical localization maps. Its proof extracts the
already proved geometric normalization equation. It is proved, with no hole.
These two small interfaces keep the source-equation extraction separate from the
large categorical pasting proof so that each file compiles within the limit.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.QuotientSectionPullTransport": "c7ecb1bd0bfdd62a3a1057351282a671acb04d81", "Sheaf.Paper.QuotientSectionPullTransportComputed": "74a672b9af05dd3625ce38745f1292da97933036", "Sheaf.Paper.QuotientSectionPullTransportGeometricComputation": "58d5b239ad52dfb1d6d5fce32340fb1837dbd711", "Sheaf.Paper.QuotientSectionPullTransportScalarComputation": "83a8c5730c1510262ada084f016eae46a41ecc92"}, "results": {"Sheaf.Paper.QuotientSectionTensorNormalization": {"hash": "60f796d6c8076d259a600d663a0828ba9b43a7a7", "status": "OK"}}, "seconds": 15, "time": "2026-10-28T05:44:35+0800", "transitive": 0, "version": 1}
```

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
