Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-topological-flasque-acyclic.json`: item split into one specialization step; no new nodes.
- `citations.json`: verbatim statement excerpts for both cited nodes.

Attachments: none.

WANTED: none; the Stacks source was available as `/home/ubuntu/c1-stacks-review/cohomology.tex` although the repository literature checkout contains only citation indexes.

The target was not an exact Lean declaration: searching both `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `/home/ubuntu/weil-conjectures-slopmaster2/WeilConjectures` found no declaration or blueprint tag for `lem-sc-topological-flasque-acyclic`. The DAG already contains `lem-sc-zariski-flasque-acyclic`, whose statement is the same flasque acyclicity theorem on a topological space in the resolution model; I therefore cited it instead of creating a duplicate child node. The item's statement and hypotheses were left unchanged. The existing `def-sc-topological-abelian-cohomology` statement explicitly identifies the opens-site cohomology with the right derived functor of global sections.

## Not duplicates

`lem-sc-topological-flasque-acyclic` vs `lem-sc-zariski-flasque-acyclic`: the former spells out the opens site and right-derived-global-sections formulation, while the latter states the same result using the Zariski/resolution notation; the former is a direct specialization of the latter together with `def-sc-topological-abelian-cohomology`.

## Review by M1

I read the source proof of Stacks Lemma 09SY in `cohomology.tex` (the injective/flasque resolution argument) and Section 01DZ's definition of cohomology. I also opened the complete statements of `lem-sc-zariski-flasque-acyclic` and `def-sc-topological-abelian-cohomology`. Step 1 uses exactly the former node's vanishing statement and the latter node's identification of H^p with the right derived functor; both quotes are copied verbatim into `citations.json`. The only elementary reasoning is that the site of opens with open coverings is the topological/Zariski site, so the two formulations refer to the same sheaf category and global-sections functor. I checked the empty space and a one-point space as edge cases: all positive cohomology groups vanish and the specialization remains valid. No statement or dependency outside the item was changed; no new node was needed because the existing DAG theorem covers the substantive argument.
## Second reading by M1

- Item statement: checked against Stacks Cohomology Section 01DZ and Lemma 09SY (lemma-flasque-acyclic), with the opens-site, flasque, and derived-global-sections hypotheses all present; verdict: agrees with the project's topological specialization.
- Step 1: checked both cited statements (`lem-sc-zariski-flasque-acyclic` and `def-sc-topological-abelian-cohomology`) verbatim and verified that they supply the vanishing and derived-functor identification; the site identification is elementary; verdict: valid.
- New nodes: none; the existing `lem-sc-zariski-flasque-acyclic` node was searched in `dag/nodes` and is cited as the generic input rather than duplicated.
- Edge cases: the empty space and one-point space have no positive cohomology in the stated derived-functor model; the quantifier `q > 0` and restriction-surjectivity definition behave correctly.
- Mathlib searches: the recorded LeanSearch-unavailable result, LeanFinder, Loogle, and Mathlib grep searches were checked against `searches.jsonl`; no exact declaration was found.
- Changes: none; the split, citations, blueprint fields, and preflight checks passed the statement, dependency, duplicate, and search checks.
