# Stage-1 report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-refined-topology-comparison-vanishing.json`: split item, with the Stacks induction proof and one dependency.
- `dag/nodes/sec-trace-formula/lem-trf-comparison-induction-step.json`: statement-only unsplit lemma for the Tag 0EZE induction step; Mathlib searches found no match.
- `citations.json`: verbatim citation for the non-elementary induction step.

## Attachments

None. No declaration tagged `(blueprint: lem-trf-refined-topology-comparison-vanishing)` exists in either read-only source checkout.

## WANTED

None.

## What was checked and corrected

The imported item had an empty proof despite citing Stacks Tag 0EZF. I read the full comparison setup (Tag 0EZ3), the definition of `(V_n)`, the induction lemma (Tag 0EZE), and the first assertion of Tag 0EZF in `literature/stacks-project/sites-cohomology.tex`. The statement's five hypotheses agree with the source situation, including base-change stability of `P`, preservation of the weak Serre classes, the tau-sheaf condition, and the specified three-stage refinement. I kept the exact item statement and supplied the missing induction argument. The only non-elementary argument is the Tag 0EZE induction step, so it is represented by the new statement-only node rather than hidden in an item step.

## Review by Q14

I checked the item source and every proof step against `sites-cohomology.tex`: Step 1 uses only the definition of `(V_0)` and is vacuous; Step 2 cites `lem-trf-comparison-induction-step`, whose statement explicitly says `(V_r) implies (V_{r+1})` under the complete comparison hypotheses; Step 3 is the direct identification of `(V_n)` with the requested range of higher direct images. The item hypotheses introduce the same topologies, comparison morphisms, classes, and derived functors as Tags 0EZ3 and 0EZF, and the new node repeats the hypothesis package needed by Tag 0EZE. I verified the new node is strictly an induction step rather than a restatement of the conclusion, searched the whole DAG and blueprint for duplicates, checked the Mathlib search logs (LeanSearch, LeanFinder, Loogle, and grep), and recorded the exact node sentence used in `citations.json`. No source or statement error was found.

## What could not be finished

The induction-step node remains intentionally unsplit, as required for a newly created stage-1 node; its complete proof is the cited Stacks Tag 0EZE proof and will be handled by a later worker.
