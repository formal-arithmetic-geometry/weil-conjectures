Files written:

- `lem-pc-ringed-space-sheafification-cohomology` (statement, split; no new nodes and no Mathlib leaves).
- `citations.json`.

Attachments: none.

WANTED: none; the source is the Stacks Project Tag 0BKJ recorded in the item.

The imported node had the correct Tag 0BKJ statement but no proof. I kept its hypotheses and dependencies, filled the blueprint place, and supplied the proof in three steps. No new node was needed: the only non-elementary input is the existing ringed-site module-sheafification exactness statement, used as a generic tool. The item has no matching declaration in the slopmaster2 Lean source (the blueprint tag and the relevant cohomology/sheafification keywords were searched).

## Review by H1

I checked the item statement against the recorded Stacks label `cohomology-lemma-sheafification-cohomology` (Tag 0BKJ), including the ringed-space, derived-object, all-degree, canonical-sheafification, and stalk-localization clauses. Step 1 uses the ringed-space cohomology definition for computation by an injective representative and the abstract derived-category definition of cohomology objects. Step 2 uses the exactness statement of `lem-weil-pbc-ringed-site-module-sheafification-exact`; its statement supplies preservation of finite limits and colimits, hence the cycle, boundary, and quotient calculation. Step 3 uses the universal sheafification definition and spells out the neighborhood colimit interpretation of a stalk, yielding both representative and eventual-zero assertions. I opened each cited node and copied the cited statement text into `citations.json`; the hypotheses are unchanged throughout. I also checked the small cases of a one-point ringed space and a zero complex: the sheafification map is the identity and the stalk clauses are immediate. The off-unit exactness lemma is declared in `split_report.tool_uses` because it is a generic ringed-site input rather than a route node of this unit.

## Second reading by H1

Item statement: checked against Stacks Tag 0BKJ, label `cohomology-lemma-sheafification-cohomology`; all hypotheses and stalk clauses agree. Verdict: correct.
Step 1: checked against the Tag 0BKJ K-injective reduction and the two cited definitions. Verdict: correct.
Step 2: checked sectionwise cycles, boundaries, and quotients against the abstract cohomology definition and the exactness tool. Verdict: correct.
Step 3: checked against Tag 0BKJ and the existing module-stalk and sheafification-stalk lemmas. Verdict: repaired and correct.
New nodes: none; existing DAG nodes were searched and reused, with no duplicate or restatement introduced. No Mathlib leaf was added.
Small cases: one-point ringed space and zero complex reduce to identity sheafification and zero cohomology.
Changes: added the missing Step 3 citations and citation quotes. The universal sheafification property alone did not support the stalk-colimit inference.
