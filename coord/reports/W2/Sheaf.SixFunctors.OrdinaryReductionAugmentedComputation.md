## What changed

Filled `WeilConjectures.OpenSemilinearTensor.ordinaryReductionAugmentedComputation`
without changing its statement, universes, hypotheses, public imports or definitions.
The only Lean file changed is the assigned module. Its node now records the actual
proof route.

The evaluation isomorphisms and quotient squares identify the given ordinary
reduction with an existing ordinary tensor/limit model. Transport that model's
adjunction and scalar-unit equation to the given functor. The fixed-calculus
comparison supplies the natural derived isomorphism and finite presentation.
The augmentation is constructed by transposing the ordinary unit through the
constant-tower/limit adjunction on complexes. A direct calculation with the
derived adjunction unit identifies the entire transpose, including the scalar
restriction factor. Thus the proof retains the strict chain augmentation,
rather than merely checking finite derived evaluations.

Proof imports are `Sheaf.Paper.CompletionUnitFixedCalculusModels`,
`Sheaf.Paper.CompletionUnitCanonicalModels`, and
`Sheaf.Paper.CoefficientExtensionOrdinaryAssociationChain`. They use `import all`
to access their already-proved implementation lemmas, without reexporting them. The canonical-model helpers used here (the termwise
limit comparison and the canonical right-derived unit) do not assume
invertibility of the residue characteristic.
The private helpers added here prove sequence-model comparison, transport of its
unit, a heterogeneous equality for equality-induced identifications, the strict
section normalization, and the constant-tower derived transpose formula. The
augmentation calculation is a proved private theorem over an arbitrary ordinary
model, so checking it does not repeatedly unfold the transported model. No other
module is adapted.

Validation: the final single-file `lcompile.py` run compiled without errors or
warnings in 45.4 seconds. Profiling options have been removed. No compile-time
or heartbeat limit was raised.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.OpenSemilinearTensor.ordinaryReductionAugmentedComputation`
(node `lem-sf-ordinary-reduction-augmented-computation`).
Original holes: 1. Holes added: 0. Holes remaining in the item: 0.
There are no split-off statements.

## No longer needed

The planned direct proof dependency `lem-sf-sequence-tensor-augmentation-unit`
(module `Sheaf.CategoryTheory.SequenceTensorAugmentationUnit`) is not used. The
existing fixed-calculus comparison derives the ordinary adjunction and gives its
normalized Hom formula; the constant-tower calculation is proved locally.
This is a removal from this item's proof route, not a request to withdraw that
module or remove its other consumers.

`lem-coef-derived-system-evaluation-calculus` remains a statement dependency and
is available through the unchanged public import. It is no longer a separately
cited proof step: the proof uses the specified calculus and the existing
fixed-calculus comparison.

No original import was removed. An exploratory private import of
`Sheaf.Paper.CompletionUnitFiniteMateComparison` was removed because its lemmas
were not used directly. No files are withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The original plan's ordinary/derived
quotient-limit argument was already available in the fixed-calculus model
implementation, so it need not be reconstructed or split again. The remaining
constant-tower transpose and strict section normalization are proved here.

The dependencies from the trace-transport and purity units are used only as
generic tools: normalized derived adjunction comparisons and assembly of
sequence-module isomorphisms from finite evaluations. They do not replace a
step of the six-functor compatibility unit. The named imported modules contain
no local `sorry` declarations. The existing public theorem's signature was
compared verbatim with the shared source and is unchanged.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
