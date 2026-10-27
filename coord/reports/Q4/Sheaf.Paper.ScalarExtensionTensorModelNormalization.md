## What changed

Implemented `WeilConjectures.ScalarExtensionTower.tensorModelRealization_normalized`
without changing its statement or the construction of `tensorModelRealization`.
The proof uses strict quotient isomorphisms for the two coherent presentations,
their tensor generator formula, naturality of the representative tensor models,
and uniqueness of the normalized Roos comparison. A proved private generic
functor-composition lemma performs the final pasting without repeatedly
rewriting the large derived-category expressions.

Added four proved support modules:
`Sheaf.Paper.CoherentReferenceQuotientComparison` identifies a coherent
presentation with the fixed ordinary quotient coordinates, and
`Sheaf.Paper.StrictQuotientTensorGenerator` computes the transported strict tensor
map on homogeneous generators. The first specializes the existing coherent
quotient comparison using a reference ordinary model and the existing
fixed-calculus derived comparison. The second is an ordinary calculation and
requires neither K-flatness nor derived coherence.
`Sheaf.Paper.CoefficientTensorModelComparison` proves compatibility of the two
normalized representative tensor models with the canonical closed-tensor
comparison. It packages the identity-curry calculation separately to keep each
file within the compilation limit. `Sheaf.Paper.ReferenceTensorModelFactors`
provides the hom equation for the four defining factors using the underlying
ordinary tensor directly. This avoids the expensive tensor-alias conversion.

Added proof imports only to the item and updated its DAG proof route. No existing
public signature, public import, definition body, or exported instance or attribute changed.
No other existing Lean module was edited.

Verified the complete set with server-mode `lcompile.py --all`: all files compile
without warnings within 60 seconds. The main module takes 38.8 seconds, and the
new reference-factor API takes 22.2 seconds. Width, debug-option and DAG signature
checks also pass.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.ScalarExtensionTower.tensorModelRealization_normalized`.

Also proved `WeilConjectures.coherentReferenceQuotientComparison`,
`WeilConjectures.ScalarExtensionTower.strictQuotientTensorGenerator`, and
`WeilConjectures.coefficientTensorModelComparison`, and
`WeilConjectures.pullbackTensorReferenceTensorModel_hom`.
There are zero remaining or added `sorry` declarations in this delivery.
The proof still uses project declarations whose proofs are separate stage-3 work.

## No longer needed

No existing module or node is withdrawn, and no original public import is
removed. The draft proof import of `CompletedQuotientReductionPresentation` was
removed because that downstream module already imports the item. Its ordinary
coordinate calculations are proved privately from `PurSequenceOrdinaryFactorization`.
The redundant draft import of `ScalarHomTensorCoherence` was also removed; its
needed generator lemma is available through the tensor-evaluation proof import.
The original planned quotient comparison is used through the new
reference-coordinate compatibility theorem. The realization-data node remains a
statement dependency rather than a separate proof step.

## Where the brief, the DAG or earlier work was wrong

The default local compiled mirror exposed an older `IsTensorModelNormalized`
without the two whole-system coherence hypotheses. The shared source and current
server source include them. The server's published artifacts also initially had
the older predicate. Verification uses the launcher's supported server mode,
`LCOMPILE_NO_LOCAL=1`, compiling an unchanged copy of the current realization-data
source immediately before the item. That copy is only a compilation input: its
bytes match the shared source, so it makes no Git change in the delivery.

The original four-step mathematical route is retained. Its ordinary quotient
coordinate calculation and tensor generator calculation were not packaged in
exactly the needed form; the new proved lemmas supply them. No statement is
disputed or weakened. The same formulas include zero complexes, the first
quotient, arbitrary degrees and the empty scheme.

## New nodes

`lem-pur-coherent-reference-quotient-comparison` records the strict ordinary
quotient identification and its whole-system derived normalization. Its proof
uses the existing quotient comparison, fixed-calculus models and canonical limit
unit; it adds no existence assumption.

`lem-pur-strict-quotient-tensor-generator` records the ordinary generator formula
for the tensor of two normalized quotient identifications. Its proof uses tensor
evaluation naturality, restriction/evaluation and the total tensor generator map
formula. Neither node contains a hole. Both retain the item's blueprint unit.

`lem-coef-representative-tensor-model-comparison` records the common-transpose
normalization of the representative tensor models. Its proof uses the existing
coefficient tensor curry normalization and closed comparison transpose equation.
It contains no hole and retains the item's blueprint unit.

`lem-pur-reference-tensor-model-factors` records the hom-component equation of
the existing four-factor reference model. It is proved from the standard Mathlib
component equations and introduces no assumption or hole.

## Related modules compiled before delivery

4 related module(s) compiled against this delivery by deliver3.py: 4 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CoefficientTensorModelComparison": "28e8b5805905b6331985a754a76da98d5f628f92", "Sheaf.Paper.CoherentReferenceQuotientComparison": "0371c9037aa13f83c51c289993a3b729c5aa2745", "Sheaf.Paper.ReferenceTensorModelFactors": "239918dfdc3369ad63ff3e1ef89605a780e10d4b", "Sheaf.Paper.ScalarExtensionTensorModelNormalization": "40862c2a33e9c805f5185df9806f2255afbcd455", "Sheaf.Paper.StrictQuotientTensorGenerator": "af2487b6e514c03dc479e52d0b27c9c1128448bf"}, "results": {"Sheaf.Paper.NormalizedIntegralGeometricCoherence": {"hash": "099fab1b1deeedbb1f753c3ec245419c23573a9e", "status": "OK"}, "Sheaf.Paper.ScalarExtensionTowerCoherence": {"hash": "86634efede6671b0de6a20ef81a609e6bc42ffc1", "status": "OK"}, "Sheaf.Paper.SystemEnrichedProjectionAdjunction": {"hash": "066c3df3f151d3b0c7cd152fe91f7f4ed1fa489b", "status": "OK"}, "Sheaf.Paper.SystemInternalHomRepresentability": {"hash": "ec888cb4582ba569e5022db79cd6017c161c76a2", "status": "OK"}}, "seconds": 251, "time": "2026-10-28T06:03:27+0800", "transitive": 3, "version": 1}
```

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
