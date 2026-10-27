## What changed

Replaced `WeilConjectures.IntegralVerdier.signedCalculus` by a proof from
`IntegralHom.models_exist`, a proved transport of Koszul symmetry, and the new
single-presentation evaluation naturality lemma. The item keeps its full statement
and public import unchanged. Its proof imports are private.

The private `transport_natural` proves conjugation naturality in an arbitrary category.
The private `presentation_symmetry` lifts the ratio of the two K-flat tensor
comparisons through the fully faithful restriction functor at the product
localization. It conjugates the ringed-site braiding by this natural isomorphism.
The proof verifies both its naturality and its signed homogeneous representative
formula, including the degree transport from j+i to i+j. `generator_transport`
identifies the two existing pure-tensor conventions.

The supplied source presentation and the finite reduction presentations are reused;
no new existence statement, coefficient presentation or construction is assumed.
The new theorem isolates the remaining first-variable naturality argument for one
arbitrary normalized presentation, so the same result applies to completed and
finite coefficients. Its source proof is Stacks 08J9 and the existing evaluation
normalization. The parent and new DAG nodes describe this argument.

## Proved and sorry left

Closed the original hole in `WeilConjectures.IntegralVerdier.signedCalculus`
(node `lem-sf-integral-verdier-signed-calculus`) by decomposition.

Added one hole: `WeilConjectures.IntegralHom.evaluation_naturality`
(node `lem-sf-integral-hom-evaluation-naturality`), in
`Sheaf.Paper.IntegralHomEvaluationNaturality`. No holes remain in the item.
The new statement is only the single-presentation evaluation identity: it assumes
its presentation, has no symmetry assertion, constructs no presentation, and has
no coefficient-reduction or simultaneous-choice assertion. The symmetry part and
the assembly of the existing presentations are completely proved.

Holes closed: 1. Holes added: 1. This is a decomposition, with zero net holes
closed, not a complete proof independent of further obligations.

## No longer needed

No existing public import is removed and no module is withdrawn.
`lem-pc-kflat-resolution` is no longer a direct proof dependency of the item:
the item reuses `IntegralHom.models_exist` for presentations and the already
proved K-flat localization for symmetry transport. K-flat resolutions remain
part of the new evaluation lemma's argument. No whole module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The original plan described constructing normalized presentations and a coherent
adjunction together, but `IntegralHom.models_exist` already supplies the
presentations. Conversely `TensorPresentation.adjunction` is a family of individual
adjunctions, and its type does not assert first-variable naturality. That identity
cannot be obtained merely by applying ordinary counit naturality, which varies
only the target. The new lemma records the needed comparison with the natural
closed adjunction using the existing representative evaluation normalization.

Edge cases checked in the mathematical argument: zero inputs, the zero ring and
empty site, negative homogeneous degrees, arbitrary unbounded complexes, and the
first positive quotient n=0. None requires a new hypothesis. The blueprint unit
record has no realized steps to bypass; its Verdier duality route is retained.

## New nodes

`lem-sf-integral-hom-evaluation-naturality` isolates evaluation naturality for a
supplied normalized presentation over a single arbitrary pro-etale ring sheaf.
Its complete argument is in its docstring and node. Searches used LeanFinder,
Loogle, LeanSearch and local source searches; Mathlib's fixed-object evaluation
naturality does not compare the separately supplied presentation adjunctions.
There are no changed definitions, statement repairs, consumer adaptations or
change records.

The new node uses `lem-pc-kflat-resolution` (another unit) as the standard
resolution tool and `lem-pur-hom-kflat-into-kinjective` (the operations unit)
as the Hom-acyclicity tool. Neither replaces a step of this unit: these supply
the representative resolution and mapping calculation needed to compare the
two adjunctions. No new `tool_uses` approval is asserted in the packet.

Validation: both sandbox modules compiled. The item also passed a single-file
compile against the compiled new lemma in 20.6 seconds, with no errors or warnings.
The existing theorem signature was checked byte-for-byte against the repository;
only proof metadata fields changed in its node.

## Second reading by X8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
