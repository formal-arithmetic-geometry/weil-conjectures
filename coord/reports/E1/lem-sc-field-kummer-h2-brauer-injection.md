1. Files written:
- `lem-sc-field-kummer-h2-brauer-injection/item.json` — statement, two proof steps, no new node; Mathlib searches found no matching etale-cohomology declaration.
- `citations.json` — verbatim citations for all step uses.

2. Attachments:
- `AlgebraicGeometry.Scheme.subsingleton_cohomologicalPicardGroup_of_field` belongs to `cor-sc-hilbert-90-field` (existing closed node).

3. WANTED:

4. What was checked and corrected:
The item was checked against the blueprint node `lem-sc-function-field-cd-one`, second proof step, and the source paragraph in `literature/blueprint/master/blueprint/sec-curve-estimates/sk-prop-h2/lem-sc-function-field-cd-one.md`. No exact declaration tagged with this item exists in `WeilConjectures`; the relevant source theorem search was also checked. The first step uses the statement of `lem-amb-kummer-any-base`, which explicitly says the etale Kummer sequence is exact for an invertible integer on any scheme; ell is invertible on Spec E because it is prime to the characteristic. The second step uses `lem-weil-pbc-derived-functor-long-exact`, whose statement supplies the exact derived-functor sequence, and `cor-sc-hilbert-90-field`, whose statement gives H^1(Spec E,G_m)=0. Exactness then gives the claimed injection. The generic Kummer and derived-functor nodes are declared as tool uses because they are off-unit black-box results. I removed an initially unnecessary `def-br` proof citation because the item statement itself only names the target as H^2(Spec E,G_m). I checked the edge case ell=1 is excluded by primality, and the argument applies equally in characteristic zero and positive characteristic.

5. What could not be finished:
No Lean proof was written at stage 1, as required. No new node was needed; all non-elementary ingredients already exist in the DAG.

## Review by E1
I read the item, its blueprint proof, `lem-amb-kummer-any-base`, `lem-weil-pbc-derived-functor-long-exact`, and `cor-sc-hilbert-90-field`. Each cited statement says exactly the fact used by its corresponding step, and every cited node exists and is unmerged. I verified the field hypothesis needed for Kummer invertibility and the zero H^1 hypothesis needed for injectivity. The search log contains LeanFinder, Loogle, grep, and an unavailable LeanSearch attempt with their actual outputs. The split has no duplicate or new helper node, and the item metadata points back to the precise blueprint sentence.
