## What changed

Proved `CategoryTheory.tor_dimension_shift_free` in
`Sheaf.Algebra.TorDimensionShiftFree`, without changing its signature or visibility.
Replaced the proof import `Sheaf.Algebra.Homology.FreeResolutionSesSplit` with
`Sheaf.Algebra.TorDimensionShiftNatural`. The latter already proves the stronger,
natural isomorphism by projective-resolution splicing and has no `sorry`.
For every positive degree, evaluate its family at the supplied coefficient module.
For degree two, use `Limits.IsZero.of_iso` in both directions.
Updated the item's node proof, proof dependencies and proof origin to match this route.
The item's unit realization does not require the discarded resolution construction.

## Proved and sorry left

Closed the sole hole: `CategoryTheory.tor_dimension_shift_free`
(node `lem-weil-pbc-tor-dimension-shift-free`). No holes remain and no holes were added.
The module compiled cleanly using the required local compiler. The delivery dry run
also checks its declarations for nonstandard axioms.

## No longer needed

Removed proof import `Sheaf.Algebra.Homology.FreeResolutionSesSplit`, corresponding to
`lem-weil-pbc-free-resolution-ses-split`. This theorem no longer constructs or uses
compatible free resolutions. The standalone resolution route's dependencies
`def-weil-pbc-free-module`, `def-weil-pbc-exact-sequence`, and
`def-weil-pbc-tor-modules` are no longer direct proof dependencies of this node;
the natural dimension-shifting theorem retains the definitions it needs.
No public statement imports were removed. No claim is made that these shared nodes
are unreachable from every other target.

## Where the brief, the DAG or earlier work was wrong

The old proof plan predates the completed stronger declaration
`CategoryTheory.tor_dimension_shift_natural`
(node `lem-sc-p1-tor-dimension-shift-natural`). Its existing proof supplies the
entire isomorphism clause, so repeating the free-resolution construction is unnecessary.
No mathematical statement error or interface change was found.

## Second reading by E2

1. I compared `lean/Sheaf/Algebra/TorDimensionShiftFree.lean` with the repository version. The theorem signature and visibility are byte-for-byte unchanged; only the proof and its proof-only import changed. Verdict: pass.
2. I compiled the delivered module with `python3 /home/ubuntu/weil-launcher/lcompile.py`; it compiles without errors or warnings, contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`, and the proof introduces no new declarations. Verdict: pass.
3. The proof uses the existing `CategoryTheory.tor_dimension_shift_natural` theorem and specializes its natural isomorphism at `N`; the degree-two vanishing equivalence is transported with `Limits.IsZero.of_iso`. No statement was split off, and no duplicate theorem was added. Verdict: pass.
4. The natural dimension-shifting theorem is the shorter route and preserves the unit route through the already realized natural dimension-shifting node. The removed free-resolution proof import and its direct dependency are no longer needed by this proof. Verdict: pass.
5. The item's node now records `lem-sc-p1-tor-dimension-shift-natural` as its sole proof dependency and describes the proof actually written; the target statement and unit realization are unchanged. Verdict: pass.

I changed the proof import, replaced the proof with specialization of the natural isomorphism, updated the node's proof metadata, and added this second-reading record. No holes were added.
