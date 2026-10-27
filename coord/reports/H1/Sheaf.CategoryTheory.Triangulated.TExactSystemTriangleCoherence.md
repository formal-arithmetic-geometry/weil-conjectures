## What changed

Proved both declarations in `Sheaf.CategoryTheory.Triangulated.TExactSystemTriangleCoherence`.
The triangle comparison is constructed directly from the normalized truncation isomorphisms,
with the upstream `Functor.eTruncGEδLT_comm` supplying the shifted boundary square.
Cutoff compatibility uses the upstream comparison equations for the EInt-indexed truncations.
An explicit triangle lift of a shift-compatible natural transformation gives its triangle square.
The existing cohomology-pasting declarations give heart membership, the formula, and naturality.

For the system theorem, truncation naturality and composition give the associator equations.
A proved private helper derives shift compatibility of the diagonal transport from the left
unit law: after substituting the diagonal functor equality, its shift comparison is an
invertible idempotent, hence the identity. This gives the actual specified diagonal triangle
transport and the diagonal cohomology equation. The system triangle equation follows on all
three components; the cohomology system equation combines naturality and composition.

Added the private proof import
`import all Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE`
to read the components of canonical cutoff maps. Removed the unused public import of the upstream Homology module. Both declaration
signatures and all definitions are preserved. There are no downstream Lean consumers;
the import change is recorded in `coord/changes/H1-texact-system-proof-imports.md`.
The node's proof and proof dependencies now describe this argument.

## Proved and sorry left

Closed 2 of 2 original holes:

- `CategoryTheory.Triangulated.TStructure.texact_triangle_cutoff_coherence`.
- `CategoryTheory.Triangulated.TStructure.texact_system_triangle_coherence`.

Both belong to `lem-per-texact-system-triangle-coherence`.
No holes remain in the delivered module. No holes were added or split off.

## No longer needed

The proof does not need `lem-pod-texact-truncation-triangle-comparison` or its module
`Sheaf.CategoryTheory.Triangulated.TExactTruncationTriangleComparison`: the normalized
comparison maps already satisfy the three triangle squares by upstream proved lemmas.
That dependency was removed from this node's proof dependencies and its obsolete
`tool_uses` approval was removed. Its module was never imported.
This does not withdraw that node or module from any other user's argument.

Removed `public import
WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology`: no declaration from that
module is used, and there are no downstream Lean modules requiring its re-export.
The other planned dependencies are retained: canonical
truncation and triangle infrastructure, normalized truncation comparison laws, and
cohomology comparison pasting. No unit statement or unit proof route was changed.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The old proof plan unnecessarily passed through the separate
full-triangle comparison theorem and reconstructed cutoff maps by TR3; upstream already proves
both the boundary equation and naturality in the EInt cutoff. The proof now uses those facts.
The diagonal shift identification in the old prose required an explicit cancellation argument;
it is proved here rather than identifying two structures merely from the underlying functor
equality. The right unit and pentagon hypotheses are preserved, although the displayed
coherence conclusions follow from the normalized comparison laws and the left diagonal unit.

Searches run through msearch: LeanFinder for t-exact truncation triangle/cutoff naturality
(found triangle constructors and mapTriangleCompIso, no whole theorem); Loogle for
CategoryTheory.Functor.eTruncGEδLT_comm (unknown identifier in its Mathlib-only index); grep
for eTruncLT_map_app_eTruncLTIso_hom_app or mapTriangleIdIso (found Mathlib identity lift).
Local searches found the stronger upstream spectral-object API actually used. Read BBD
1.3.3--1.3.6 and the current blueprint unit; the construction preserves the stated boundary,
heart shift, and literal unit transport, including coincident cutoffs and diagonal indices.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
