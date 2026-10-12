## What changed

Proved `RingTheory.exists_ideal_filtration_length_one` in
`lean/Sheaf/Paper/ArtinianIdealLengthOneFiltration.lean`. The proof uses the Mathlib
Artinian finite-length equivalence, the existing simple-filtration theorem for the
ideal viewed as a module, and an explicitly constructed linear equivalence between
successive quotients after mapping submodules along the ideal subtype.

Added the proof-only import `Mathlib.RingTheory.HopkinsLevitzki`.

## Proved and sorry left

Closed `RingTheory.exists_ideal_filtration_length_one`. No `sorry` remains and no
new holes were added.

## No longer needed

No imports or proof-dependency nodes were removed. The proof uses both the
Artinian self-module finite-length result (via its Mathlib declaration) and
`Module.exists_simple_filtration_of_length_lt_top`.

## Where the brief, the DAG or earlier work was wrong

Nothing was wrong. The DAG route is followed; the submodule-to-ideal translation
and quotient equivalence are supplied directly in the proof.

## New nodes

None.

## Second reading by R2

1. Compared the delivered module with the repository version. The theorem signature and
   all existing declarations are unchanged byte for byte; only the proof and a proof-only
   `Mathlib.RingTheory.HopkinsLevitzki` import were added.
2. Compiled the module with `lcompile.py`; it compiles cleanly with no warnings or
   remaining `sorry`. The proof introduces no axioms or unsafe declarations. The route
   uses the Artinian-to-Noetherian instance and the finite-length simple filtration, then
   an explicit quotient linear equivalence.
3. The existing theorem is the only statement delivered, and no split-off statements or
   new nodes were added. Its hypotheses and conclusion are exactly the reviewed DAG
   statement; no Mathlib or upstream duplicate was introduced.
4. Checked pruning and imports. The new Hopkins--Levitzki import is used only by the
   proof to obtain the Noetherian instance. The two public imports and the simple
   filtration import remain necessary for the signature or proof, and no proof-dependency
   node is removed.
5. The proof follows the unit route through finite length and simple filtration, and the
   DAG node's `proof` and `proof_deps` remain accurate. No definition or target statement
   changed.

Changed: restored the original module documentation while retaining the completed proof;
no mathematical or interface changes were needed.
