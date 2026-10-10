1. Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-torsor-h1-boundary-representative.json` — statement split into three proof steps; no Mathlib leaf.
- `dag/nodes/sec-curve-estimates/lem-sc-zariski-ext-torsor.json` — new statement-only Zariski extension/torsor bridge; Mathlib no match.
- `citations.json` — verbatim statement quotes for every cited node and step.

2. Attachments: `CategoryTheory.Sheaf.nonempty_equiv_H_one_torsor` belongs to `lem-sc-torsor-h1`; this is already recorded in the item source node and is not an exact declaration of the present Zariski boundary statement.

3. WANTED: none.

4. What was wrong or incomplete: the imported item had no proof and its nearest existing extension node `lem-sc-ext-torsor` is explicitly stated for the etale site. Reusing it for the Zariski site would violate C4, so I added `lem-sc-zariski-ext-torsor` as a statement-only bridge. The proof now follows Stacks Lemma 02FQ: contracted powers construct the extension, the long exact sequence supplies the boundary of 1, and the converse identifies the fibre torsor. No statement was weakened.

## Review by M1

I read the item record, the ancestor `lem-sc-pic-proper-ntorsion`, the existing Zariski torsor node `lem-sc-torsor-h1`, the extension construction `lem-sc-ext-torsor`, and `def-sc-topological-abelian-cohomology`. I also read the source reference used by the imported proof, Stacks Cohomology Lemma 02FQ, and checked that the item’s statement is the Zariski version of its boundary-of-one construction.

Step 1 uses only the new Zariski extension/torsor statement: it supplies the contracted-power coproduct, exactness, and fibre over 1. Step 2 uses that same bridge for the extension class, `lem-sc-torsor-h1` for the canonical H^1/torsor bijection, and `def-sc-topological-abelian-cohomology` for the natural long exact sequence and its connecting map. Step 3 uses the fibre-over-1 clause, the same H^1/torsor bijection, and the long exact sequence. These statements say exactly the facts quoted in `citations.json`; no step is marked elementary because each invokes sheaf cohomology or torsor classification.

For the new node I checked B1–B7: it is statement-only, introduces X, the Zariski site, G, E, and Z_X, cites the definitions it uses, uses the Stacks tag and label as source, records LeanSearch, LeanFinder, and Mathlib grep searches with no match, and has the required blueprint ancestry and empty same-as search. I searched the whole DAG and blueprint for `torsor boundary`, `contracted powers`, `02FQ`, and the relevant declarations before creating it. I tested the construction on the trivial torsor (it gives the split extension and boundary zero) and on the identity coefficient map; both recover the expected fibre and class. I corrected the initial plain-arrow notation to TeX arrows before running the checks.

5. What I could not finish: no Lean proof was required at stage 1, and the Stacks source checkout is represented by the project’s cited tag metadata rather than a local `cohomology.tex` file.
