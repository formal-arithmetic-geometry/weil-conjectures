## What changed

Repaired the tensor normalization domain in
Sheaf.Paper.ScalarExtensionTowerRealizationData: both simultaneous input presentations
must satisfy the existing IsIntegralComparisonPresentationCoherent predicate.
This matches the current server's repaired scalar and pullback normalizations and
excludes the documented invisible-presentation-twist defect. The generator formula,
Roos equation, coefficient data and completed operations stay identical.

Constructed WeilConjectures.ScalarExtensionTower.tensorModelRealization explicitly in
Sheaf.Paper.ScalarExtensionTensorModelNormalization. It transports the existing uniquely
strict-Roos-normalized pullbackTensorIntegralTensorModel through the canonical reduction
left-adjoint comparison and the transpose-preserving closed-tensor comparison. It does
not select an arbitrary isomorphism from a mere existence theorem. Normalization of this
specific construction is the sole new smaller theorem.

Assembled realizationModels from that constructed tensor isomorphism and its normalization,
and the existing primitiveQuotientScalarModelExistence theorem. Restored the source's
invertibility hypothesis to realizationModels. Its sole caller,
Sheaf.Paper.IntegralScalarPullbackCounitCompatibility, already has the required instances;
its two applications now supply them by Bool cases. Every public signature and import
in that caller stays identical. The main scalarExtensionTowerCoherence signature,
all existing strict/quotient proofs, and every Challenge signature stay identical.

Added only two private proof imports to the item: the new tensor normalization module
and PrimitiveQuotientScalarModelExistence. No existing public import is removed.
The dependency module and the caller were unclaimed when checked on the server.
The change record is coord/changes/M3-tensor-presentation-coherence.md.

Validation: the repaired data module, explicit construction, item, and adapted caller
compile through lcompile.py. Fresh runs took 22.7 s, 4.2 s, 43.6 s, and 14.8 s
respectively. The unchanged direct importers ScalarTowerPullbackLimitSquare,
ScalarTowerTensorLimitSquare, CompletedComparisonQuotientRealizationDefs, and
IntegralComparisonSystemData compile against this chain (46.4 s and 51.1 s for the
last two). The unchanged RationalRealizationTensorComparison exceeded the limit at 69 s;
its profiler run also exceeded it at 64.8 s (68.2 s cumulative kernel type
checking, 19.9 s cumulative elaboration). No declaration in that file uses
the changed predicate or theorem. It is not edited in the delivery; the delivery
baseline comparison determines whether this is pre-existing. All
unchanged validation copies are removed from the delivered packet.

## Proved and sorry left

This is a statement/interface repair and a decomposition, not a proof of the old false
normalization or a net hole reduction. There was one item-module hole before the repair:
WeilConjectures.ScalarExtensionTower.realizationModels. Its corrected statement has a
complete proof from the two model constructions and has no direct sorry. Because its
normalization domain and missing source hypothesis are repaired, this report does not
count the original statement as proved unchanged.

The new explicitly constructed tensor natural isomorphism
WeilConjectures.ScalarExtensionTower.tensorModelRealization has no hole in its data or
proof. The scalar half uses the existing stated theorem, without adding any scalar hole.

One hole is added, and is the only sorry in the delivered Lean files:
WeilConjectures.ScalarExtensionTower.tensorModelRealization_normalized,
node stage3-pur-scalar-tensor-model-normalization, in the new module
Sheaf.Paper.ScalarExtensionTensorModelNormalization. It concerns only the local-generator
and whole-tower Roos equation for a fixed constructed tensor realization, with no scalar
extension, no simultaneous two-location model choice, and no remaining descent existence
problem. Its full source and proof in words are in its docstring and node.

Direct holes removed from the item: one, by the corrected assembly above. New holes: one.
Net change: zero. Original statement proved unchanged: zero of one. Split off: one.
The already completed square, unit, quotientModels and scalarExtensionTowerCoherence
proofs are retained.

## No longer needed

The obsolete proof-plan edge to lem-pur-normalized-scalar-comparison-realization is removed.
Its attached NormalizedScalarComparisonRealization module is absent from both the
current source and rework list, as the earlier B4 report also found. This packet does
not import it, withdraw it, or change its node. Its entire aggregate theorem is unnecessary
for the model-existence assembly: use the existing scalar-model theorem and the narrower
constructed tensor normalization instead. No other parent dependency or unit route is
bypassed. No module is withdrawn; no globally pruned module is claimed. No existing
public import is removed. The unchanged direct-importer copies used for validation are
not part of the delivery.

## Where the brief, the DAG or earlier work was wrong

The current server queue has one disputed hole. The shared snapshot queue still listed
two and the build-error file describes obsolete bad imports from October 24. The current
module compiles, so those old import messages are not the mathematical defect.

The server's current IsIntegralComparisonScalarNormalized already includes the whole-system
coherence condition (J5), while an early local read still showed its preceding version.
Only the tensor predicate needs that repair here. Its original finite-evaluation tests
do not fix the entire derived comparison: the T6 example twists a presentation by a
nonidentity derived-complete automorphism whose finite derived reductions are identities.
With the other tensor input the coefficient unit, the same defect affects tensor
normalization. Requiring the existing double-adjunction-transpose coherence corrects
exactly that presentation domain. Canonical coherent presentations exist for every good
input, including zero objects, the first quotient, and empty schemes. This is a sourced
auxiliary-interface correction, not a Lean-certified counterexample or a silent proof of
the original clause. The definition node records the correction and every current citer.

The source node assumes l invertible on X,Y; realizationModels omitted it. The added
hypothesis belongs only to that auxiliary existence theorem. The sole caller already
has both residue-field invertibility instances, so its theorem does not gain a hypothesis.
The target-meaning review of any target using this auxiliary model interface should
confirm the corrected canonical presentations describe the same maps. No target
statement, coefficient ring, completed operation or quotient map is changed.

Separate existing issue for the maintainer/holder T1: the current
primitiveQuotientScalarModelNormalization statement quantifies over an arbitrary realization
isomorphism and claims every one is normalized. Even after the coherence-domain repair,
a scalar multiple of the canonical realization need not satisfy its fixed Roos equation.
The true primitiveQuotientScalarModelExistence contract used here only asks for a normalized
model. This delivery does not alter that held module or use the overstrong normalization
lemma directly. Its holder should restrict that subsidiary theorem to its constructed
realization, as the new tensor normalization lemma does. This is reported for independent
review rather than silently adapting an unrelated held signature.

## New nodes

stage3-pur-scalar-tensor-model-normalization records the explicitly transported tensor
realization and its remaining normalization theorem. The existing uniquely normalized
reference tensor, canonical comparison of reductions, and canonical comparison of closed
tensors supply actual data; only the strictly smaller tensor-generator/Roos equation
remains. The node records LeanFinder, Loogle, LeanSearch, and local/library searches and
retains the original source's realization step. It is not realizationModels renamed.

Change record: coord/changes/M3-tensor-presentation-coherence.md.

## Related modules compiled before delivery

5 related module(s) compiled against this delivery by deliver3.py: 3 INFRA, 2 OK.

```json
{"capped": false, "direct": 5, "left_out": 0, "own": {"Sheaf.Paper.IntegralScalarPullbackCounitCompatibility": "61bcd707c7ef0c477f456ea32bd77c5e283ac2de", "Sheaf.Paper.ScalarExtensionTensorModelNormalization": "4b57fb2dac2a53c8e5e04c3e71fe33455eb50ccf", "Sheaf.Paper.ScalarExtensionTowerCoherence": "86634efede6671b0de6a20ef81a609e6bc42ffc1", "Sheaf.Paper.ScalarExtensionTowerRealizationData": "140422ac41c53c1983f8b2c40c684f43557860d6"}, "results": {"Sheaf.Paper.CompletedComparisonQuotientRealizationDefs": {"hash": "dfdfeed46ace6c4c802b28ac2734d71c9bcc5602", "status": "INFRA"}, "Sheaf.Paper.IntegralComparisonSystemData": {"hash": "6983e6f589bb81180a511d6f951b69864c960e26", "status": "INFRA"}, "Sheaf.Paper.RationalRealizationTensorComparison": {"hash": "fb60a875f5ff45bb9046ae9766520bd1ffded299", "status": "INFRA"}, "Sheaf.Paper.ScalarTowerPullbackLimitSquare": {"hash": "9b8e25d96f17214d7907bbec84a30465ce6559fe", "status": "OK"}, "Sheaf.Paper.ScalarTowerTensorLimitSquare": {"hash": "eb39c8230a4fbd499e5460ed3456e39a715f496f", "status": "OK"}}, "seconds": 76, "time": "2026-10-28T02:30:07+0800", "transitive": 0, "version": 1}
```

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
