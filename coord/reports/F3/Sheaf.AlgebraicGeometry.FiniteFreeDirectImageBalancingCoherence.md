## What changed

Proved `AlgebraicGeometry.Scheme.FiniteFreeDirectImage.finiteFreeDirectImageBalancingCoherence`
with its original statement. Added proved private helpers in the item module; no other
library module or public declaration signature changes.

The proof identifies the normalized scalar multiplication and associators with the
canonical adjunction unit and composition isomorphisms. It proves identity and tower
coherence for the restriction/direct-image comparisons from their normalization, then
transfers these equations to balancing through conjugation. Flat-term K-flat
resolutions establish the needed identification of the model adjunctions with the
derived Hom-comparison adjunctions. All added imports are private proof imports.

Updated `lem-sp-finite-free-balancing-coherence`'s proof, proof dependencies and proof
origin to describe this route. No definitions, statements, or source-library modules
were changed. The complete item module compiled through `lcompile.py`
with exit code 0 in 28.1 seconds on the earlier attempt and in 21.2 seconds on
this resumed attempt. Added change record
`coord/changes/F3-finite-free-balancing-proof-context.md` for the local proof
commands flagged by preflight; the public theorem statement remains unchanged.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.Scheme.FiniteFreeDirectImage.finiteFreeDirectImageBalancingCoherence`
(node `lem-sp-finite-free-balancing-coherence`). No holes added or split off. No
`sorry` remains in the item module. Imported statements retain their existing proof
status; this delivery introduces no new assumed result.

## No longer needed

No original import was removed and no module is withdrawn. The proof no longer uses
the old plan's direct calculation of pullback on pure tensors. Its direct DAG proof
dependencies therefore no longer include:

- `def-pur-sheaf-tensor-product`;
- `lem-pur-derived-change-of-rings`;
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`;
- `lem-weil-pbc-localization-universal-property`.

The existing statement interfaces may still import these transitively; this delivery
does not claim those modules are globally unnecessary. It retains the K-flat
resolution and successive quotient normalization dependencies, and names the derived
Hom-comparison, restriction/direct-image, tensor exactness, and mate calculus results
used by the actual proof.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically sound, but its explicit pullback-on-tensors
calculation is unnecessary: balancing is defined as conjugation of the normalized
right comparison. Coherence of that right comparison and uniqueness of normalized
adjoints give the two required equations directly. No disputed statement or process
failure was found. No unit-level route or target statement changed.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
