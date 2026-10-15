## What changed

The requested module was already proved and landed by H1 in commit `b85896bd00`.
This sandbox preserves that proof and removes its redundant local use of the torsion
hypothesis: the binder is named `_hF` and the proof no longer needs `have _ := hF`.
The theorem type and all mathematical hypotheses are unchanged; this only silences
Lean's unused-variable warning.

## Proved and sorry left

`AlgebraicGeometry.Etale.exists_cohomology_class_of_isLimit` is sorry-free (it was already
closed in the shared repository). No `sorry` was added.

## No longer needed

The old `have _ := hF` proof line is no longer needed. No import or DAG dependency was
removed.

## Where the brief, the DAG or earlier work was wrong

The assignment was stale: the H1 proof had already landed and the node records a reviewed
proof from 2026-10-15. The delivery therefore contains no newly closed hole.

## Earlier second reading (a previous round; superseded)

The source-level binder rename preserves the theorem's type and all hypotheses. The
existing proof compiles cleanly, and the downstream caller is unaffected because Lean
binder names are not part of application elaboration. The change record lists the only
interface-text difference for independent review.

Change record: `coord/changes/exists_cohomology_class_of_isLimit.md`.

## Second reading by D4

1. **Interface comparison:** compared the delivered module with the shared repository.
   The theorem statement and mathematical hypotheses are unchanged; the only source-level
   difference is the declared binder rename `_hF`, recorded in the change record.
   Verdict: pass.
2. **Proof and axioms:** compiled the module locally with `lcompile.py`; the theorem has no
   `sorry`, and `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.
   No forbidden declarations or hollow definitions occur. Verdict: pass.
3. **Statements and searches:** no statement was split off or added. The existing DAG node is
   true, has the required strength, and its recorded Mathlib and library searches remain
   applicable; no duplicate declaration was introduced. Verdict: pass.
4. **Pruning and route:** the proof uses both recorded proof dependencies and keeps the
   `sk-prop-h2` unit route. The removed `have _ := hF` was redundant; no import or DAG node
   can be pruned. Verdict: pass.
5. **DAG agreement:** the node's statement, proof steps, proof dependencies, and origin agree
   with the delivered proof. The binder rename is interface-text-only and is covered by
   `coord/changes/exists_cohomology_class_of_isLimit.md`. Verdict: pass.

Changed only the unused torsion binder spelling and its redundant proof line; no holes were
added or newly closed, and no imports or nodes were removed.
