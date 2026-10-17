## What changed

Repaired the returned proof of
`AlgebraicGeometry.schemeDerivedDirectImage_preserves_QCoh_of_isGE` in
`Sheaf.AlgebraicGeometry.DerivedDirectImageBoundedBelowQCoh`. The proof now compiles
against the current upstream synchronization. The finite filtration helper uses the
current `PBCDecreasingFiltration` interface and the current named argument of
`Scheme.Modules.isQuasicoherent_of_shortExact`; the page induction and spectral-sequence
argument are retained and compile unchanged. The `CategoryTheory.Limits` opening remains
because the proof uses the limits API.

## Proved and sorry left

Closed the one original `sorry`:
`AlgebraicGeometry.schemeDerivedDirectImage_preserves_QCoh_of_isGE`, node
`lem-pc-derived-direct-image-bounded-below-qcoh`. No new `sorry`s or split-off statements
were added, and no `sorry` remains in the delivered module.

## No longer needed

None. Every proof import in the module is used by the completed route; no DAG node or
module was pruned.

## Where the brief, the DAG or earlier work was wrong

The returned version was based on a module whose filtration API had been removed by the
upstream synchronization. The helper therefore had to be adapted from
`DecreasingFiltration` to `PBCDecreasingFiltration`, and the extension theorem call had
to pass its short complex with `(S := C)`. These are proof-local repairs; target and
public theorem signatures are unchanged. The DAG proof route remains accurate.

## Earlier second reading (a previous round; superseded)

The repaired module compiles against the current shared source, preserves the target
statement and public signatures, closes the original hole without adding any `sorry`,
and follows the node's four-step route. The proof-local API adaptations are recorded in
`coord/changes/derived-direct-image-bounded-below-qcoh-open.md`.

## Second reading by B4

1. **Comparison with the repository.** I compared the delivered module with the
   repository version. The public theorem signature and the two existing private
   helper signatures are unchanged byte for byte. The previously commented-out
   filtration helper is restored with `PBCDecreasingFiltration`. The namespace
   opening affects proof name resolution; no definition, public signature, or
   public import changes. Verdict: pass.

2. **Compilation and proof status.** The module compiles with
   `python3 /home/ubuntu/weil-launcher/lcompile.py`. The original
   `schemeDerivedDirectImage_preserves_QCoh_of_isGE` hole is closed; no `sorry`,
   `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` was added, and no
   definition contains a hole. In a scratch copy I ran `#print axioms` on the
   theorem and all three private helpers: each reports exactly `propext`,
   `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Verdict: pass.

3. **Statements and split-offs.** No new public or private theorem statement was
   split off. The repaired filtration helper is private and is a genuine
   intermediate induction, while the target statement remains exactly the DAG
   statement. The induction also handles N = 0: the full initial step is already
   zero. For n < a the chosen bound is 0, and the convergence hypotheses supply
   both endpoints. Searches of the library and a fresh Mathlib grep search found
   no shorter applicable preservation theorem; the existing higher-direct-image,
   kernel, cokernel, and extension results are reused. Verdict: pass.

4. **Route and pruning.** The proof follows all four DAG steps: bounded-below
   representative and truncation spectral sequence, quasi-coherent E2 terms,
   page induction, and finite-filtration extension. The current upstream API
   requires `PBCDecreasingFiltration`; the old commented helper used a removed
   `DecreasingFiltration` interface. All proof imports remain used, so there are no
   pruned imports or nodes. Verdict: pass.

5. **DAG agreement.** The node's statement, proof dependencies, source, and proof
   origin still describe the delivered proof. The implementation uses exactly the
   listed declarations and leaves no additional node or hole requiring a DAG entry.
   The unit record is unchanged; the proof does not bypass any unit step. Verdict:
   pass.

The first worker's proof repairs pass this reading. I changed only this report,
adding the independent review and its validation evidence; I made no further Lean
or DAG changes.
