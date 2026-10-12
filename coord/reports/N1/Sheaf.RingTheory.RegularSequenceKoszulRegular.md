## What changed

Filled the proofs of `RingTheory.Sequence.IsRegular.isKoszulRegularOn` and
`RingTheory.Sequence.IsRegular.isKoszulRegular`. The first theorem,
`isKoszulRegularOn_of_isWeaklyRegular`, remains the foundational induction theorem
with its existing `sorry`; both corollaries now apply it via
`IsRegular.toIsWeaklyRegular`. The ring corollary transports homology vanishing
through the canonical tensor-unit chain-complex isomorphism.

## Proved and sorry left

Proved:

- `RingTheory.Sequence.IsRegular.isKoszulRegularOn`
- `RingTheory.Sequence.IsRegular.isKoszulRegular`

Sorry left:

- `RingTheory.Sequence.isKoszulRegularOn_of_isWeaklyRegular` (the existing node
  `lem-weil-pbc-regular-sequence-koszul-regular`)

## No longer needed

No imports or DAG nodes were rendered unnecessary. The proof uses the existing
Koszul-complex definitions, the regular-sequence API, and the tensor-unit
chain-complex isomorphism.

## Where the brief, the DAG or earlier work was wrong

Nothing identified.

## Second reading by N1

1. Compared the delivered module with the repository version: existing theorem
   statements and definitions are byte-for-byte unchanged; only the two proof
   bodies are filled.
2. Compiled `Sheaf.RingTheory.RegularSequenceKoszulRegular` with the prescribed
   launcher. It compiles cleanly, with no new `sorry`, `axiom`, `unsafe`, or
   forbidden declarations. The two completed corollaries depend on the already
   open foundational theorem, so the expected `sorryAx` remains only through that
   theorem.
3. Checked the proof route against the imported declarations and Mathlib's
   `IsRegular.toIsWeaklyRegular`; the module-level corollary is a direct
   specialization, and the ring-level corollary uses the canonical
   tensor-with-unit chain-complex isomorphism. No new statement was split off.
4. The imports are minimal for the signatures and proof: the two public imports
   provide the predicates and regular-sequence API, while `Sheaf.Paper.KoszulComplex`
   is proof-only. No old proof dependency or module became unnecessary.
5. The unit route and existing DAG node are preserved. The foundational
   induction theorem remains the sole sorry listed by the report, with its
   existing node and source documentation.

Changed only the proofs of `IsRegular.isKoszulRegularOn` and
`IsRegular.isKoszulRegular`, and added this second-reading record.
