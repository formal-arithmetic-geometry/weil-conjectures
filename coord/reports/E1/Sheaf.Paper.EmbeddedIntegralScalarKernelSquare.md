## What changed

Proved `AlgebraicGeometry.ProEtale.embeddedIntegralScalarKernelSquare` with its
recorded signature unchanged. The proof recovers a coefficient ring isomorphism
from one-point sections, proves the scalar square by adjunction counit naturality,
constructs the residue quotient square, and transports kernel ideals through its
section-ring isomorphisms. All auxiliary declarations are private and proved.
The existing public imports are preserved; a private proof import supplies
quotient-ring equivalences.
The existing node's proof is updated to describe these constructions. No definition,
public interface, target statement, or other module is changed.

## Proved and sorry left

Closed the one assigned hole:
`AlgebraicGeometry.ProEtale.embeddedIntegralScalarKernelSquare`
(node `lem-sfb-embedded-integral-scalar-kernel-square`).
No holes remain in the delivered module; no holes are added or split off.
The existing DVR and kernel-ideal APIs are used as stated. The induced coefficient
ring isomorphism is arbitrary: no canonical choice or norm compatibility is assumed.
The quotient square and its inverse identify kernels even on empty site objects;
the general kernel argument uses only the local ideal-extension characterization.

## No longer needed

No declared dependency, module, or unit step is pruned. All four existing proof
dependencies remain needed. No derived-completeness lemma, exactness assertion
for sheafification, or new intermediate obligation is needed for this underived
square: functoriality and the local characterization of ideal extension suffice.
No source-library declarations are removed.

## Where the brief, the DAG or earlier work was wrong

At the start the assigned Lean file was absent from the shared checkout, although
its node retained the full Lean signature and the queue listed its one hole.
There was no matching rework or quarantine row or current return. During work the
source file arrived by synchronization with the same recorded statement. The delivered
module restores that exact recorded statement and proves it; its attachment and
dependencies are preserved. The DAG's suggested exactness argument is unnecessary:
a commuting square with isomorphisms identifies the kernels directly.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
