## What changed
Added a core intermediate theorem recording the limit-descent construction with an explicit compatibility witness, and reduced the target theorem to its first conjunct.

## Proved and sorry left
The target theorem `exists_finiteEtale_lift_of_henselianPair_of_gRing_lifting` is proved from the core theorem. The new theorem `exists_finiteEtale_lift_of_henselianPair_of_gRing_lifting_core` remains `sorry` (node `lem-weil-pbc-finite-etale-lifting-limit-descent-core`).

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The eight-step construction in the DAG is substantially longer than can be encoded directly in the available statement modules; it was split at the construction boundary.

## New nodes
`lem-weil-pbc-finite-etale-lifting-limit-descent-core` records the remaining limit-descent construction.

## Earlier second reading (a previous round; superseded)
The target proof compiles and uses the intermediate theorem. The intermediate statement is a strict strengthening by retaining an explicit compatibility witness; the unit route and parent statement are unchanged.

## Second reading by E2
1. Compared the delivered module with the repository version: the target signature is byte-for-byte unchanged; only its proof and the explicitly delivered core module/import were added. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py`; the only remaining `sorry` is the named core theorem. No forbidden declarations occur. The target theorem's axioms are inherited from that split theorem. Verdict: pass subject to the recorded split.
3. Checked the split statement and its node. The added conjunct `Nonempty (Y ≅ Y)` is true by the identity isomorphism and the core theorem projects to exactly the target conclusion. Verdict: pass as a true strengthening, with the construction itself intentionally left open.
4. Read the proof route and imports. The proof uses the core theorem only; no old proof dependency can be pruned without also removing the intended unit route. Verdict: pass; no imports or nodes pruned.
5. Checked DAG metadata, module/declaration names, and unit `sk-thm-p1`; the node and Lean declaration agree and the parent statement/unit route are unchanged. Verdict: pass.

Changed only this review record; no Lean proof or statement was altered during second reading.

## Earlier second reading (a previous round; superseded)
The target proof compiles and uses the intermediate theorem. The intermediate statement is a strict strengthening by retaining an explicit compatibility witness; the unit route and parent statement are unchanged.
