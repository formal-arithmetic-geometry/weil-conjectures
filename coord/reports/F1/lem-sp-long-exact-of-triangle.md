# Stage-1 report: lem-sp-long-exact-of-triangle

## Files written

- `dag/nodes/sec-abelian-varieties/lem-sp-long-exact-of-triangle.json` — statement, split proof, Mathlib search record.
- `citations.json` — one verbatim citation for the proof step.

## Attachments

None. No sorry-free project declaration in `WeilConjectures/` carries the blueprint tag or the exact statement.

## WANTED

None.

## What was wrong or incomplete

The imported proof was only a compressed sketch. I expanded the iteration over all rotations, identified the connecting morphism, and stated why naturality follows. The item is not a Mathlib leaf: Mathlib's `Functor.IsHomological` API gives indexed exact segments only after an explicit `ShiftSequence`, so it is a related generalization rather than an exact match. No new subordinate node is required; the only non-elementary input is the existing definition node `def-sp-homological-functor`.

## What could not be finished

Nothing.

## Review by F1

I read the item source at `literature/blueprint/master/blueprint/sec-abelian-varieties/sk-prop-av-pqf-finite/lem-sp-long-exact-of-triangle.md` and checked the corresponding blueprint paragraph. I read `dag/nodes/sec-abelian-varieties/def-sp-homological-functor.json`; its statement explicitly supplies exactness for a distinguished triangle and for the next rotated segment, which is exactly what Step 1 uses. The step also uses only the pretriangulated definition that rotations remain distinguished and ordinary functoriality, both stated in the item's hypotheses/definition context, so no additional node is needed. I checked the Mathlib source `Mathlib/CategoryTheory/Triangulated/HomologicalFunctor.lean`: it contains `IsHomological`, `homologySequenceδ`, and three indexed exactness lemmas, but its extra `ShiftSequence` interface means it does not state this unindexed item exactly. I tested the edge cases conceptually: a zero functor gives the zero long exact sequence, and a triangle together with one rotation supplies adjacent exact segments with the same connecting map. The citation quote is verbatim from the definition node.

## Second reading by F1

- Item statement: checked against the imported blueprint node and its stated hypotheses; the homological-functor and abelian-category dependencies are explicit, and the displayed sequence and naturality clause are unchanged.
- Step 1: checked against `def-sp-homological-functor`; its two exactness clauses supply each rotated segment, and the repaired text explicitly indexes rotations, identifies the shared endpoint maps, and proves naturality via commutative squares from a morphism of triangles.
- New nodes: none; there are no new statements to audit under B1--B7, and a repository-wide search found no duplicate fact that should be introduced as a node.
- Mathlib check: `CategoryTheory.Functor.IsHomological` and the `homologySequence_exact_1/2/3` declarations in `Mathlib/CategoryTheory/Triangulated/HomologicalFunctor.lean` provide an indexed `ShiftSequence` generalization, not this unindexed statement; the worker's recorded searches are retained, including the unavailable LeanSearch result.
- Small cases: the zero functor gives a zero exact sequence; for a zero distinguished triangle every map is zero; rotation at $n=0$ and $n=1$ gives adjacent segments with the same connecting morphism.

Changes made: expanded Step 1 to replace “repeat the same argument” and “naturality follows” with the rotation-by-integer construction, endpoint concatenation, and the functorial commutative-square argument. No statement, source, dependency, or citation was changed.
