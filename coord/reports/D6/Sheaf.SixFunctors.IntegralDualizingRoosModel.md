## What changed

Completed `WeilConjectures.integralDualizing_roos_model` without changing its statement
or any existing definition. The finite terms and transitions are exactly the published
exceptional-inverse-image terms and counit transitions. Their existing comparison theorem
supplies the unit, cocycle and invertibility properties. Normalization is the composite
of precomposition by an isomorphism with the scalar-adjunction Hom equivalence.

Added two proved modules, imported privately by the proofs:
`Sheaf.Paper.NormalizedDVRCompletedRestrictionCoherence` proves the unit and associativity
equations for the specified completed restriction comparisons, using the existing exact
localization coherence API; `Sheaf.Paper.NormalizedDVRStrictRealization` constructs a
strict realization by K-injective representatives and successor chain maps, followed by
transposition from a diagram of complexes to a complex of diagrams.

Private helpers in the item compare auxiliary evaluation with canonical derived
evaluation and transport the existing Roos triangle. The product isomorphism is built
from its component maps and inverses, so the proof uses the required published product
witness even when it differs from the witness in the limit specification.
All original public imports, declaration signatures and definition bodies are retained.
Private evaluation wrappers express the Roos transport proof over the unrestricted
coefficient category throughout; the final application identifies them definitionally
with the specified normalized evaluations and transitions. No exported attribute changes. The associativity cancellation is proved for abstract exact functors
before specialization, avoiding repeated unfolding of the coefficient constructions.

## Proved and sorry left

Closed the original hole in `WeilConjectures.integralDualizing_roos_model`: 1 of 1.
Added 0 holes. There are no remaining `sorry` declarations in any delivered Lean module.
Validation: all three modules compiled individually in import order without warnings,
within the 60-second limit; the item compiled in 24.5 seconds.
The two new public theorems are fully proved:
`WeilConjectures.normalizedDVR_completedRestriction_coherence` and
`WeilConjectures.normalizedDVR_strict_realization`. No obligation was split off.

## No longer needed

Removed no imports and withdrew no module. Removed the original node's direct proof
edge to `lem-pc-quasi-isomorphisms-multiplicative-system`: the explicit construction
now uses K-injective representatives and the proved Hom computation into them.
This is removal of a direct edge from this node, not withdrawal of that Mathlib leaf
or of any source-library declaration that uses it. The new strict-realization node
records the Grothendieck/K-injective input. All other original mathematical dependencies
remain. The blueprint unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The old roof-construction paragraph did not supply a simultaneous strict sequence:
choosing a roof for the next map can replace its source, so compatibility with the
already chosen complex requires further work. The proof instead chooses K-injective
targets first, which represent every successor derived arrow by an actual chain map.
Only successor maps must be chosen; finite composites and `Functor.ofOpSequence`
give every longer transition and `NatTrans.ofOpSequence` proves its compatibility.

The canonical completed restriction comparisons also need explicit coherence equations.
The existing general exact-derived compositor and natural-isomorphism API proves them;
no altered comparisons or additional hypotheses are used. Repeated indices, identity
transitions, zero objects and the empty scheme obey the same identities. Strictification
uses unbounded K-injective resolutions, so no boundedness or flatness assumption enters.

The historical build-error record concerned unavailable dependency artifacts. The
unchanged starting file compiled against the current published artifacts; the work
therefore addressed its actual proof hole rather than changing its public imports.

## New nodes

`lem-coef-normalized-dvr-completed-restriction-coherence` records the proved equations
for the specified restriction comparisons, including degenerate cases. Its theorem
is in `Sheaf.Paper.NormalizedDVRCompletedRestrictionCoherence`.

`lem-coef-normalized-dvr-strict-realization` records the proved strict realization
of arbitrary coherent finite coefficient systems. It requires neither normalization
nor a Roos triangle, and is strictly a construction step of the original argument.
Its theorem is in `Sheaf.Paper.NormalizedDVRStrictRealization`.

Updated the original node's proof, proof dependencies and proof origin to match the
Lean construction. No definition/statement change record is needed.

## Related modules compiled before delivery

6 related module(s) compiled against this delivery by deliver3.py: 6 OK.

```json
{"capped": false, "direct": 3, "left_out": 0, "own": {"Sheaf.Paper.NormalizedDVRCompletedRestrictionCoherence": "c56ed4fb9ff7bbb485440d47f6f0c53bfba3069e", "Sheaf.Paper.NormalizedDVRStrictRealization": "50fa2aad7e24ac7f6446e54506b51a9cafc0ba92", "Sheaf.SixFunctors.IntegralDualizingRoosModel": "ab44d1b2ed785b4ad72bcbddd26bb5b87c1b4d6c"}, "results": {"Sheaf.Paper.AdicPuritySourceNormalization": {"hash": "5761f642fca161633f4421b1894da06d1caeb049", "status": "OK"}, "Sheaf.Paper.FiniteScalarRepresentativeIso": {"hash": "f3fed952a8ba8a38c2f3a861ec55435c5533560c", "status": "OK"}, "Sheaf.Paper.RamifiedScalarSystemTranspose": {"hash": "53ac490826ec5a0fa35c7c8f9a5ca4c9b3fca77d", "status": "OK"}, "Sheaf.SixFunctors.IntegralDualizing": {"hash": "d5a8d27fec1bc1bd0f759a9b9f9246ffc3702622", "status": "OK"}, "Sheaf.SixFunctors.IntegralDualizingFiniteBounds": {"hash": "b2a8e3df239cf54ffce078a0ccd32bbfd4068ec8", "status": "OK"}, "Sheaf.SixFunctors.IntegralDualizingMappingLimit": {"hash": "d26d9ff982c4d655794d0fa3a8a31add588e5931", "status": "OK"}}, "seconds": 259, "time": "2026-10-28T01:14:58+0800", "transitive": 3, "version": 1}
```

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
