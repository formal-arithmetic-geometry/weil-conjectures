## What changed

Implemented WeilConjectures.podReindexingTensorSubstitutionCore by constructing the
completed-operation model on the two Bool locations. Its calculus, completion and
Roos fields are exactly the supplied D fields. Its selected g-pullback is D.pullback
with D.PullbackNormalization; other arrows use the existing primitive normalized
pullback construction. CompletionUnits gives its completion-unit field.

The proof imports all of NormalizedCompletedOperationModels and
CompletedOperationTowerSubstitution privately, to reuse their already proved
modelCounit/modelUnit/modelTensor/modelPullback and expression-induction helpers
with this fixed model. It also privately imports PrimitiveQuotientRealizationComparisons.
No existing generic proof module is edited or restated. A declaration-local unused-variable
lint setting preserves the existing hT parameter and the named existential witness
core in the result True; both names are intentionally unused.

Repaired the two tensor equations in PodReindexingTensorSubstitutionCoreData and
PodReindexSubstitution. Their old HEq compared isomorphisms with independently
chosen tensor codomains. The new podReindexTensorCodomainComparison is a concrete
canonical isomorphism of those codomains, built from the common internal-Hom
adjunction and uniqueness of the reduction left adjoint. The equations now assert
equality after this specified comparison. Then qY/qX are constructed by composing
the fixed strict-tower realization with the two inverses. This preserves the
strict-tower normalization, with no free comparison map.

The primitive D.limit equation is proved for every system: cancel D.pullback,
use naturality of D.limit at the actual source counit, then apply the source
adjunction's right triangle identity. No D.Counit, normalized-input hypothesis,
or tensor law is needed for this calculation. The fixed model satisfies the
existing primitive normalization proofs, hence the existing comparison,
substitution and structural proofs apply to it directly.

The two node records describe this route and explicitly record the tensor
interface correction and its citers. The unit sk-def-weil has no realized steps
changed. No file under lean/WeilConjectures or Challenge.lean is changed.
Change record: coord/changes/C4-pod-reindex-tensor-codomain.md.

Validation through lcompile.py, one file at a time in import order, with no warnings:
PodCompletionReindexSubstitution 1.7 s; PodReindexingTensorSubstitutionCore 12.8 s;
unchanged PodReindexingTensorSubstitution 5.6 s; unchanged
PodReindexingCompletionUnitTensor 34.6 s. All are under 60 s. The unchanged consumer
copies were removed from the sandbox after checking; only the two changed Lean
modules are delivered. The import-direction check passes.

## Proved and sorry left

Closed the single textual hole in
WeilConjectures.podReindexingTensorSubstitutionCore
(node lem-pod-reindexing-tensor-substitution-core), for the repaired tensor
presentation interface described above. The theorem's binder list and stated
result type are unchanged, but the tensor fields of its result structure are
explicitly repaired; this is not a claim to have proved the former stricter HEq
specification.

Holes closed: 1. Holes added: 0. Split-off statements: 0. Sorries left in either
delivered Lean module: 0. Existing imported proof dependencies may still depend
on their separately assigned holes; none is replaced or duplicated here.

## No longer needed

No original import is removed and no module or node is withdrawn. The generic
completed-operation substitution node is retained: its expression-induction
proofs are applied to the fixed model. The tensor Laws hypothesis remains in the
public theorem interface, though this core construction does not use it; the
parent theorem separately retains T.Model and T.Canonical. The old proposed
D.Counit computation is replaced by naturality and the right triangle identity.

## Where the brief, the DAG or earlier work was wrong

The previous tensor HEq fields silently required equality of independently chosen
tensor presentations. Canonical adjunction comparison supplies an isomorphism,
not such equality. The generic Models interface had already been corrected to
canonical closed-tensor comparison in the 2026-10-25 statement_change of
lem-pur-normalized-completed-operation-models. This delivery makes the fixed-D
predicate agree with that presentation convention. The change record includes
the old/new definitions and all downstream modules; no downstream source needs
an adaptation. The equations still uniquely determine qY and qX by cancellation.

Edge cases: Bool keeps the two locations distinct even when X = Y or g is the
identity; the selected arrow is then still exactly g. Empty schemes cause no
nonemptiness requirement. The generic expression laws include empty input
families. The limit calculation holds on unnormalized inputs as well.

Mathlib search: LeanFinder for fixed reduction-adjunction completed-operation
models found no applicable theorem. Loogle confirmed
CategoryTheory.Adjunction.left_triangle_components. The library search found the
existing private generic law proofs, which are reused through proof-only import all.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.PodCompletionReindexSubstitution": "9b73166f9a8704384a218246202a8b2667e7843d", "Sheaf.Paper.PodReindexingTensorSubstitutionCore": "4c7c32a5b9604ab0b6fa1d259e0ab98ddb4247f6"}, "results": {"Sheaf.Paper.PodReindexingCompletionUnitTensor": {"hash": "6f89febbb6bfe7b7a78964b1f7236b01edd9f8cf", "status": "OK"}, "Sheaf.Paper.PodReindexingTensorSubstitution": {"hash": "97fc13c2dd93af8a59d5387903cbd70b02194ae0", "status": "OK"}}, "seconds": 107, "time": "2026-10-28T08:06:02+0800", "transitive": 0, "version": 1}
```

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
