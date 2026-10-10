# Delivery report

Files written:

- `dag/nodes/sec-curve-estimates/lem-galois-fpqc-refinement-fully-faithful.json`: repaired statement node, split; no Mathlib leaf.
- `dag/nodes/sec-curve-estimates/lem-galois-fpqc-singleton-fully-faithful-0241.json`: new statement node, unsplit; no Mathlib match.
- `dag/nodes/sec-curve-estimates/lem-galois-fpqc-pullback-canonical-iso.json`: new statement node, unsplit; no Mathlib match.
- `citations.json`: verbatim statement excerpts for every proof-step citation.

Attachments: none. Searching the slopmaster2 Lean source by item id and descent-data terminology found no scheme-level declaration stating this item or either new node; hence there is no closed attachment to verify against the transitive sorry map.

WANTED: the local Stacks source snapshot `literature/stacks-project/descent.tex` and `topologies.tex` is absent in this clone. I read the Stacks web statements and proofs of Tags 02W0, 0241, 02VS, 023Y and 022D directly.

The returned proof's Step 2 used `lem-galois-fpqc-morphisms-descend` with the wrong base-change objects and did not use the descent datum; its Step 3 tried to descend along `h\\times h`, which is not fpqc in general. I removed both steps, the unused proof dependency and the off-unit `tool_uses` entry. For a counterexample take $S=\\operatorname{Spec}k$, $X=\\operatorname{Spec}k[t]$, and $X'=S$ mapping to the origin. The item statement itself is unchanged. The initial sandbox repair mislabeled 02VS and 023Y as 023Z; this repair corrects those references and states the composition comparison used in Step 2.

## Review by F1

I read Stacks Descent Lemma 02W0 (lemma-refine-coverings-fully-faithful) for the item: its two fpqc singleton families and map $h$ match the hypotheses, and its conclusion is unchanged. For the first new node I read Lemma 0241 (lemma-fully-faithful): the covering $r:X'\\to X$ is fpqc and its base scheme is the same $S$, precisely its two hypotheses. For the second I read Lemma 02VS (lemma-pullback-family), part (3), and Lemma 023Y (lemma-pullback), parts (1)--(2). They provide the comparison for two maps over $S$ and the pullback construction; the composition clause follows by associating the two fibre products in 023Y(1). Neither new node contains a proof. I searched the DAG, blueprint, and Lean source for both before retaining them; LeanSearch, Loogle, and Mathlib-source grep records are in the nodes.

Step 1 cites `def-pc-fibre-product` for the projections and `lem-galois-fpqc-covering-base-change` for the exact 022D(3) conclusion that the projection families cover. The hypotheses are checked separately: $p$ changes base of $g:X'\\to S$ along $f:X\\to S$, and $q$ changes base of $f$ along $g$. Step 2 cites `lem-galois-fpqc-singleton-fully-faithful-0241` for full faithfulness of each projection's pullback, then `lem-galois-fpqc-pullback-canonical-iso` for both the comparison of $p$ with $h\\circ q$ and the composition identification with $F_qF_h$. Both maps have source $X''$, target $X$, and the same composite to $S$; the composition clause applies to $h:X'\\to X$ and $q:X''\\to X'$. Step 3 uses only the full faithfulness and faithfulness established in Step 2; it writes out lifting and uniqueness without another cited fact. The exact sentences used from every cited statement are in `citations.json`.

For small cases I checked $h=\\mathrm{id}_X$, $X=S$, and empty schemes: both projection coverings and the comparison remain defined, including vacuous descent categories in the empty case. The origin-map example above checks why the removed $h\\times h$ claim fails. I corrected the two wrong Stacks tags, malformed TeX in the 0241 helper, and the missing composition clause found while checking C4.
