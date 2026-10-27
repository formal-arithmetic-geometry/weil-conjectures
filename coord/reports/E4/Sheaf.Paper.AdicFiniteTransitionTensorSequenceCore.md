## What changed

Replaced the single proof hole in `Sheaf.Paper.AdicFiniteTransitionTensorSequenceCore`
without changing its public theorem signature or its public imports. The proof chooses a
flat-term K-flat representative of the ambient derived object and uses the canonical
kernel sequence of its actual strict successor. A proved private helper establishes that
this successor is epic by lifting constant coefficient sections and applying tensor
extensionality. The existing strict-level comparisons and
`adicFiniteStrictReduction_successor` supply the required normalized transition square.

Added `Sheaf.Paper.AdicFiniteTransitionKernelTensor`. Its coefficient module is the actual
kernel of `A/J^(n+2) -> A/J^(n+1)`. A complete proof that J annihilates this kernel gives
its quotient A/J action; constant-module sheafification constructs the coefficient sheaf.
These definitions contain no holes and choose no witness from an existence theorem.

A second proved private helper in the item applies the existing independent-coefficient
tensor cancellation, the single-factor complex tensor comparison and exact restriction
on homology. The main proof then transports tensor homology to the supplied residue
model using the proved `coefficientModelTensorTest_iso`. Only the ordinary flat-tensor
kernel identification is left as a new statement. The item's node now records this
actual route. No other existing module or interface changes.

## Proved and sorry left

Original hole replaced by a complete Lean proof:
`AlgebraicGeometry.Scheme.adicFiniteTransition_tensor_sequence_core`
(node `lem-sfb-adic-finite-transition-tensor-sequence-core`). The item's module now
contains zero sorry proofs. Its three private helpers (constant surjectivity, successor
epimorphism and homology transport) are proved, not additional assumptions.

New proved public theorem:
`AlgebraicGeometry.Scheme.adicFiniteCoefficientKernel_annihilated`.

One new hole remains:
`AlgebraicGeometry.Scheme.adicFiniteTransitionKernel_tensor`
(node `lem-sfb-adic-finite-transition-kernel-tensor`). Its complete source-based proof plan
is in its docstring and node. It asserts only an ordinary kernel-complex isomorphism for
a complex with flat terms. It has no ambient derived object, arbitrary chosen residue
model, K-flatness assumption, endpoint comparisons, normalized transition square or
homology conclusion. The completed Lean assembly proves all those additional parts.
Thus this is a strict decomposition, not the original theorem renamed or repackaged.

Accounting: one upper hole replaced, one lower hole added, net zero; one decomposition,
not an independent hole elimination. The already stated
`AlgebraicGeometry.Scheme.adicFiniteStrictReduction_successor` is reused as intended by
stage 3; its existing hole is neither changed nor counted as a newly added hole here.

Both final Lean modules compiled through the remote compiler: 9.4 seconds for the new
module and 23.3 seconds for the item. No local Lean or Lake command was used.

## No longer needed

None. No original import, declared dependency, module, or node is withdrawn. The original
reduction-data and coefficient Tor-model dependencies remain needed. No source-library
declaration is removed. The one new hole replaces only the ordinary kernel-identification
part of the original plan; no additional derived reduction, tensor cancellation or
representative-independence lemma is restated.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The earlier one-step proof plan combined several
separate tasks without a usable coefficient-kernel interface. The new proof supplies the
actual coefficient data, epimorphism, normalized comparisons and homology transport,
and isolates the remaining ordinary interface explicitly. The unit route remains the
Stacks 09C2 coefficient-kernel argument; no unit statement or target is changed.

Edge cases checked in the constructions and proof plan: J=0 gives a zero coefficient
kernel and identity reduction; J=A gives zero quotients; n=0 uses J/J^2 with its actual
A/J action. Zero rings, empty sites and arbitrary complex degrees introduce no excluded
hypothesis. Termwise flatness suffices for the remaining kernel lemma.

## New nodes

`lem-sfb-adic-finite-transition-kernel-tensor` in
`dag/nodes/sec-six-functors-basics/` is realized by the new module
`Sheaf.Paper.AdicFiniteTransitionKernelTensor`. It includes the explicit coefficient
module construction, proved annihilation, and the ordinary flat-tensor kernel statement.
Its proof specifies the algebraic sequence, exact constant sheafification, the existing
extension-tensor comparison with its pure-tensor normalization, and assembly of the
natural degreewise kernel isomorphisms. LeanSearch, LeanFinder/Loogle, source searches
and a whole-blueprint search found no existing statement of this interface. The nearby
completed-coefficient sequence requires a Noetherian hypothesis and does not record its
quotient arrow; the principal regular-element tensor sequence does not cover arbitrary
ideals. Its blueprint ancestry is the recorded chain to `det-lem-integral-models-stacks`.
No change record is required: no other existing module or node was changed.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
