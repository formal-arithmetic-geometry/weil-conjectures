## What changed

Kept the statement of `WeilConjectures.OpenSemilinearTensor.openSemilinearOrdinaryComparison`
unchanged. Its proof now uses the existing `purSequenceOrdinaryFactorization` on X and U,
retaining the ordinary pullback functor, additivity, evaluation and quotient equations.
It combines coefficient transport, ordinary tensor transport and strict scalar transport.
The finite natural isomorphisms are constructed by evaluating and conjugating the single
strict-system isomorphism. Their component equation is proved by cancelling the evaluation
isomorphism with its inverse; the supplied scalar-generator equation gives the generators
field of `IntegralOpenReduction.TensorComparison`.

Added `OpenOrdinaryTensorTransport`, with a proof of the ordinary two-module tensor formula.
The proof constructs the coefficient pushforward tensorator using the existing presheaf
restriction tensor isomorphism and the sheafification unit, proves its pure-tensor formula
and naturality, and composes it with the normalized slice projection formula. The equivalence
counit gives exactly the `restrictedSection` in the interface. No shared module or definition
is changed. All new imports of the item are proof imports.

The generic coefficient tensorator and site-tensor helpers are in
`OpenCoefficientTensorPushforward`. Its public theorem asserts the tensor natural
isomorphism for a continuous cocontinuous site functor and an invertible coefficient
map, together with its identity-on-pure-sections equation. The composition with the
open projection formula is proved over abstract ring sheaves in
`OpenRingedCoefficientTensorTransport`; this prevents the completed coefficient limit
from unfolding inside the tensor construction. The scheme-specific module simply
instantiates that proved result and identifies the recorded summand formulas.

Added two strictly smaller remaining transport statements, in separate modules with complete
proofs in words and DAG records. `OpenCoefficientOperationsExistence` asserts existence only of the
coefficient operations, retaining invertibility of the completed coefficient map.
`OpenStrictScalarTransport` takes those operations and quotient-compatible ordinary
reductions as inputs and asserts only the normalized strict scalar isomorphism. The finite
comparison construction in that module is explicit and contains no hole.

## Proved and sorry left

Closed the original hole of
`WeilConjectures.OpenSemilinearTensor.openSemilinearOrdinaryComparison` (one original hole).
The assembly from the remaining statements is complete Lean. Also proved the new theorem
`WeilConjectures.OpenSemilinearTensor.openOrdinaryTensorTransport` and its private construction,
section and naturality lemmas. The new
`WeilConjectures.OpenSemilinearTensor.coefficientTensorPushforwardExists` is also proved;
it introduces no hole. The new
`WeilConjectures.OpenSemilinearTensor.ringedCoefficientTensorTransport` proves the
abstract normalized open formula, also with no hole.

All six delivery modules compiled with the required `lcompile.py`. The final item
compiled in 40.4 seconds and the concrete tensor wrapper in 45.7 seconds. Profiling
options have been removed. The final categorical cancellation is proved abstractly
and instantiated by definitional conversion.

Two new holes remain, each exactly a public theorem proved by `by sorry`:

- `WeilConjectures.OpenSemilinearTensor.openCoefficientOperationsExistence`, node
  `lem-sf-open-coefficient-operations-existence`.
- `WeilConjectures.OpenSemilinearTensor.openStrictScalarTransport`, node
  `lem-sf-open-strict-scalar-transport`.

This is a decomposition of the original theorem, not an axiom-free proof of it. There are
zero holes in the item module and two holes in the delivered modules. No definition contains
`sorry`, and no arbitrary object is defined by choosing a witness of an unproved existence
statement.

## No longer needed

No modules are withdrawn and no public imports are removed. None of the original mathematical
steps is pruned: the two remaining transport nodes retain the coefficient and scalar steps,
and the ordinary tensor step is proved. The item uses the existing sequence factorization
rather than reconstructing the two ordinary reductions inside the scalar transport.
`lem-coef-semilinear-derived-sections` remains a statement dependency: its data are supplied
as an argument, and the proof does not invoke its existence theorem a second time. Its module
is already public through the unchanged data interface and is not globally pruned.
The direct proof import `Sheaf.Paper.SemilinearDerivedCalculus` was moved from the new
ordinary tensor module to its generic coefficient tensor helper. The proof imports
`Sheaf.CategoryTheory.RingedSliceTensorGenerators` and
`Sheaf.Algebra.Homology.ScalarHomOrdinaryTensorComparison` are now used inside the abstract
ringed transport module. Their mathematics is still used; these import moves prune no node.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original plan's generic slice statements do not literally
have the actual coefficient-site transports as their conclusions. The explicit transport
work is needed: a bare existence of an unnormalized monoidal isomorphism would not establish
the specified original-summand equation. The ordinary tensor proof retains the normalized
presheaf and sheafification maps for this reason.

Edge cases checked when stating the two remaining theorems: identity open immersion,
empty open, zero module, and no flatness or completeness. The site equivalence and
sheafification unit constructions still apply to the empty open; the generator equations
are zero for a zero module. Ordinary scalar reductions may be presented through arbitrary
compatible evaluation isomorphisms: the conjugation by those very evaluations is essential,
and their quotient equations give coherence in the strict system category. No reduction
is chosen independently at each coefficient.

## New nodes

`lem-sf-open-coefficient-operations-existence`: the coefficient transport part of original
proof step 1, with no tensor or scalar comparison in its conclusion.

`lem-sf-open-ordinary-tensor-transport`: the ordinary tensor part of original proof step 2,
proved from the normalized slice tensor formula and the concrete coefficient pushforward.
The input invertibility is retained by the coefficient construction.

`lem-sf-open-strict-scalar-transport`: the scalar part of original proof step 3, for supplied
operations and ordinary reductions. Its conclusion is a strict isomorphism with only its
scalar-unit normalization. The original theorem additionally constructs the operations,
reductions, finite comparison record and independent ordinary two-module tensor family.

`lem-sf-open-coefficient-tensor-pushforward`: the proved generic coefficient tensorator
and its naturality, with private section and site-tensor helpers used by the open formula.
It is separated from the scheme calculation to meet the per-file compilation limit;
there is no additional remaining obligation.

`lem-sf-open-ringed-coefficient-tensor-transport`: the proved ordinary open formula over
abstract ring sheaves and a module coefficient equivalence, with the original-summand
normalization and naturality. The scheme-specific theorem instantiates this result;
no new remaining obligation is introduced.

The item node's proof, proof dependencies and proof origin follow this assembly. All five
new nodes use the same unit route and blueprint source as the original node. No change
record is needed: existing signatures, definitions, attributes and public imports are unchanged.

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
