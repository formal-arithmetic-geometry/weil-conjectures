## What changed

Replaced the proof hole in
`WeilConjectures.AdicQbarRealization.AmbientHomEvaluation.adic_ambient_hom_evaluation_comparison_coherence`
by a calculation from the source finite-stage evaluation square. The proof derives
realized finite evaluation by tensorator naturality, derives finite comparison by
injectivity of ambient transposition, proves signed symmetry from braiding
naturality and the given symmetry equation, and proves extension, tower and
identity by functoriality and cancellation of the specified gamma isomorphisms.
The proof does not use constructibility or the core comparison theorem.

Added a public import of `Sheaf.Paper.CommonStageEvaluationFiniteSquare`: its
proved object-equality API is used in the public definition of `gammaH`.
That new module isolates source finite-stage evaluation normalization, before realization
and without the geometry, constructibility, ambient Hom, or coherence conclusions
of the item. All existing public signatures and public imports are preserved, and all
definitions keep their values.
To keep each file within 60 seconds after local opacity improvements, the four
existing private uncurry/evaluation proofs and six new categorical proofs live
in the new module under `CoherenceCalculus`; the item uses that proved API.
The proved `commonStageDerivedInternalHom_obj_eq` API avoids repeatedly expanding
the chosen Hom functor and its full unique-existence predicate. `gammaH` changes
only its equality proof argument, with identical value by proof irrelevance; see
`coord/changes/H4-ambient-hom-object-identification.md`.
These ten generic results introduce no holes and their proofs are the same
calculations that type-checked in the unsplit item.
Local irreducibility of the chosen common-stage Hom and the other functors prevents the coherence proof from expanding the realization
and tensor, rational Hom, and ambient Hom functors. These attributes do not
change the exported API.
The coherence node now describes the calculation actually written and attaches
CoherenceLaws rather than the unrelated CoreLaws structure.

The final `lcompile.py --all` check passes both delivered modules and the
unchanged sole direct importer `Sheaf.Paper.AdicQbarConstructibleRealization`
(15.4 seconds). The first clean compile of the item after the object-equality
repair took 58.6 seconds; the support module took 12.6 seconds. The temporary
consumer copy was removed after testing. No debugging profiler options remain.

## Proved and sorry left

This is a decomposition: one original hole closed and one strictly smaller hole
added; net zero holes closed. The item originally has two holes, not three: its
ambient-adjunction theorem is already proved on the current source.

Closed:
`WeilConjectures.AdicQbarRealization.AmbientHomEvaluation.adic_ambient_hom_evaluation_comparison_coherence`
(node `lem-sf-adic-ambient-hom-evaluation-comparison-coherence`).

Untouched original hole:
`WeilConjectures.AdicQbarRealization.AmbientHomEvaluation.adic_ambient_hom_evaluation_comparison_core_bounded`
(node `lem-sf-adic-ambient-hom-evaluation-comparison-core-bounded`).

Added hole:
`WeilConjectures.commonStageEvaluation_finiteSquare`
(node `lem-sf-common-stage-evaluation-finite-square`). Its docstring gives the
finite-field representative proof, including scalar units, the specified Hom
comparison, and eventual equality; no faithfulness of finite-stage inclusions is
assumed. The original coherence conclusion is proved from this square, rather
than restated under a different name.

## No longer needed

No existing public imports, modules or public declarations are withdrawn.
The four existing private evaluation helpers are replaced by the proved
`CoherenceCalculus` API in the new module. The new source-square
module imports `DerivedAutomorphismHomEvaluationContinuationA` for the
normalization definition; it does not need the later declarations of the full
`DerivedAutomorphismHomEvaluation` module. Debugging imports of
`GeneralAlgebraicallyClosedCoefficientStages` and `Mathlib.Logic.Small.Defs`
were also removed from the item. The coherence proof
needs neither the core constructibility result nor the core comparison package.
Its old direct proof dependencies
`lem-sf-adic-finite-realization-cocone`,
`lem-sf-ringed-derived-tensor-hom-adjunction`, and
`lem-sf-adic-common-stage-hom-transpose` are replaced by the source finite-stage
square: the remaining argument uses the already supplied tensor input and the
ambient closed adjunction. This does not prune these nodes from the library:
all three are still cited by the untouched constructibility obligation. The
source square uses its assumed normalization directly at the requested field,
whose bound on the Hom stage also bounds the required tensor stage.
No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The coherence node's old proof discussed constructibility and invertibility,
which are the core package rather than the coherence fields. It is replaced by
the finite evaluation, transposition, symmetry, and gamma-cancellation argument.
The recorded global-build error is a bad import of NativeAdicRealizationData;
the unchanged item compiles against the current published dependencies, so this
assignment is treated as proof work, as its current queue row specifies.

Mathlib searches through msearch used LeanSearch, LeanFinder, Loogle and grep.
They found generic adjunction, braiding and closed-subcategory APIs, but no theorem
for this common-stage finite-field normalization. The repository search also
checked CommonStageEvaluationNaturality, NormalizedCommonEvaluationForStructure,
CommonStageInclusionTensorComparison and PodReindexingHomCoefficientDescent.
Those give naturality, normalization definitions, or a different evaluation
convention, rather than the required source finite-stage square.

## New nodes

`lem-sf-common-stage-evaluation-finite-square`, in
`dag/nodes/sec-six-functors/lem-sf-common-stage-evaluation-finite-square.json`,
is the finite evaluation square of step 7 of the ambient comparison. Its Lean
record also lists the proved object-identification API and ten proved generic
support lemmas in `CoherenceCalculus`.
Its module
is `Sheaf.Paper.CommonStageEvaluationFiniteSquare`. The statement uses exactly
the existing source operations and specified inclusion tensorator. Its proof
plan applies inverse-transpose normalization to the identity representative,
uses rational evaluation and the inclusion tensorator's scalar-unit formula,
and compares the two representatives at the requested common finite field. Repeated
fields, zero objects and empty schemes impose no extra hypothesis. The new node retains
the main item's unit `sk-prop-sf-biduality-general`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.AdicAmbientHomEvaluationComparison": "5c7a2c8b15060f4aaf00612f654ed85f90231635", "Sheaf.Paper.CommonStageEvaluationFiniteSquare": "dd6daa5a7a36c1b9b83a9e69fd7cfa074fd15389"}, "results": {"Sheaf.Paper.AdicQbarConstructibleRealization": {"hash": "7e2ce2076ec6ff2ae7f31dd670b20fca6d09af3f", "status": "OK"}}, "seconds": 25, "time": "2026-10-28T12:37:14+0800", "transitive": 0, "version": 1}
```

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
