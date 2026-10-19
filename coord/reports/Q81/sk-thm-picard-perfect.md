1. Files written:

- `dag/nodes/sec-picard-framework/sk-thm-picard-perfect.json` — repaired statement node, no new nodes; Mathlib searches found no exact match.
- `dag/units/sk-thm-picard-perfect.json` — realized statement and three proof steps.
- `citations.json` — verbatim citations for every step/node use.

2. Attachments:

None. The three slopmaster2 declarations named in `lean_audit.slopmaster2` are individual clauses (openness, vanishing, and finite local freeness) and do not state the complete item, which also includes the general bounded-complex statement, arbitrary derived base change, and functorial characterization. They are therefore not exact attachments.

3. WANTED:

None.

4. What was wrong in the imported node or blueprint:

The imported proof cited `sk-thm-picard-coherence` and `sk-thm-picard-semicon` but left the perfect-locus and functorial arguments implicit, and its first step relied on a “matrix calculation” without identifying the existing perfect-locus statement. I replaced it with three complete steps that cite the existing DAG statements supplying those facts. I also removed the stale `status: imported`, filled the blueprint ancestry and unit realization, and recorded Mathlib searches for the item. No statement correction was needed.

5. What I could not finish:

No unresolved split or missing source remains. The source declarations still depend transitively on `sorry` declarations in slopmaster2, so they cannot be used as finished attachments under the stage-1 attachment rule.

## Review by Q81

I read the current item node, the unit record, the main-20261015 blueprint section and proof, and the source modules containing the three slopmaster2 declarations. The item statement agrees with the blueprint general form and curve specialization, including proper finite-presentation hypotheses, flatness, arbitrary base change, the two rank loci, and the no-reducedness conclusion. The existing `sk-thm-picard-coherence` statement explicitly supplies a bounded finite-free complex and formation commuting with every base change; `sk-thm-picard-semicon` explicitly supplies upper semicontinuity; `lem-pc-perfect-locus` explicitly supplies the open fixed-degree rank criterion; and `lem-pc-flat-rf-open` explicitly supplies the functorial open-locus characterization. I checked each proof step against those exact statements and quoted the relevant sentences verbatim in `citations.json`. Step 1 verifies the curve hypotheses and derives invertibility, vanishing, and base change from the cited perfect and rank-locus statements. Step 2 verifies the bounded-complex reduction, finite intersection of upper-semicontinuity opens, and local single-degree finite-free model. Step 3 verifies both directions of the factorization criterion by fibre dimensions and the cited functorial statement. I tested the edge cases `r=0` (acyclic degree-i locus) and `i` outside the bounded complex range; the statements correctly give the empty or acyclic locus. I corrected the imported proof's uncited appeals to a matrix calculation and to the functorial characterization, and did not create duplicate nodes because all needed lemmas already exist in the DAG.
