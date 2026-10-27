## What changed

Proved `CategoryTheory.exists_ringedKoszul_finiteHomTower_iso` with its original
statement. The proof works in ordinary complexes with arbitrary coefficients.
Private proved helpers show dualizability of each two-term factor and its finite
tensors, contravariant naturality of the signed internal-Hom comparison, and
naturality and invertibility of evaluation. The resulting natural isomorphism
includes every inverse transition. A degreewise identity isomorphism identifies
the tensor diagram with the transposed strict tower complex.

The four added imports are private proof imports of existing source-library
and Mathlib results. No adopted source file, public signature, definition, or public import
changed. The node proof records this implementation using existing dualizability
and closed internal-Hom APIs.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.exists_ringedKoszul_finiteHomTower_iso`, node
`lem-weil-pbc-ringed-koszul-finite-hom-tower`.

No holes added, no split-off statements, and zero direct holes remain in the item.
Every private helper is proved. This is a proof of one original hole, not a
renaming or decomposition. Existing dependencies are used through their APIs;
this report does not claim to close any of their holes.

## No longer needed

None. Both declared dependencies are retained and used. No existing import,
node, module, unit statement, or unit proof step is withdrawn. The explicit
subset-indexed matrix calculation is supplied by the existing bounded-complex
duality and signed Hom-comparison theorems rather than duplicated here.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The DAG plan can be implemented using the existing
proved ordinary-complex duality APIs. It requires no K-injectivity, localization
of a generator, derived duality theorem, or limit comparison. The empty list uses
the monoidal unit; zero or invertible sections give the same dualizability proof.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
