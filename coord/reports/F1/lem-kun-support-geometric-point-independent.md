Files written:

- `dag/nodes/sec-smooth-purity/lem-kun-support-geometric-point-independent.json`: statement, split proof, and one Mathlib search record; no new nodes.
- `citations.json`: verbatim statement excerpts for every cited node in every step.

Attachments: none.

WANTED: none.

What was wrong or incomplete: the imported proof placed the factorization, the common indexing category, and the vanishing conclusion in one paragraph without making the cofinality argument explicit. It also used the field-embedding fact without a node citation. I split those arguments into three steps and cited the existing Mathlib leaf `lem-exc-etale-embedding-extension-sepclosed`. The item has no matching sorry-free declaration in `~/weil-src-slopmaster2/WeilConjectures`.

What I could not finish: no source markdown file is present at the path recorded in the imported blueprint, so the proof origin remains the blueprint path and its indicated `## Proof` paragraph.

## Review by F1

I read the item node, its unit and chapter records, the imported proof paragraph, and the statements of `lem-kun-stalk-as-pullback`, `def-weil-pbc-inverse-image`, `def-weil-pbc-geometric-stalks`, `def-kun-support`, and `lem-exc-etale-embedding-extension-sepclosed`. Step 1 uses only the stalk-as-pullback statement and the inverse-image definition, and the factorization through `Spec kappa(x)` supplies the hypotheses. Step 2 uses the geometric-stalk colimit definition and the embedding-extension leaf; the target fields are separably closed, so finite separable residue extensions have split minimal polynomials, which matches the leaf's assumptions. Step 3 uses the same colimit definition for the common index category and the support definition's geometric-stalk criterion.

I checked that the cited quotes are verbatim in the node files and that every proof dependency is listed. I searched the whole DAG for the item and its field/cofinality ingredients; no duplicate node states this result, and no new node was needed. I tested the indexing claim on the cases `x = Spec(kappa(x))` with both geometric fields equal to a separable closure, and on a finite separable extension embedded in two separably closed fields. The required LeanFinder, Loogle, and Mathlib grep searches were run for the item; they found only unrelated etale-locus declarations and the generic geometric-point fibre definitions, so the item remains non-Mathlib.

## Second reading by F1

- Step 1 checked against `def-pd-separable-closure` and `lem-exc-etale-embedding-extension-sepclosed`: a fixed separable closure of `kappa(x)` embeds into each separably closed geometric-point field, giving a common geometric point; verdict: repaired.
- Step 2 checked against `lem-weil-pbc-inverse-image-stalk-germ` and `def-weil-pbc-inverse-image`: each stalk is canonically identified with the stalk at the common geometric point by the inverse-image stalk isomorphism and composition; verdict: repaired.
- Step 3 checked against `def-kun-support`: simultaneous vanishing implies independence of the support criterion; verdict: pass.
- The item statement was checked on a field, the empty scheme, the zero sheaf, and equal geometric points; verdict: pass.
- No new nodes were present; the existing dependency statements and the two citation excerpts were checked verbatim.

Changes: replaced the unsupported finite-separable-extension cofinality paragraph with the common-separable-closure comparison, added the existing inverse-image stalk lemma and separable-closure definition to the proof dependencies, and updated citations accordingly. The original paragraph's cofinality claim was not justified by the cited geometric-stalk definition.
