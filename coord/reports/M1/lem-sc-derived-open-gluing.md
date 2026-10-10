1. Files written:

- `dag/nodes/sec-picard-framework/lem-sc-derived-open-gluing.json` — statement, split proof, and blueprint fields updated.
- `dag/nodes/sec-picard-framework/lem-sc-derived-open-restriction-pushforward.json` — statement-only child, no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-derived-hom-mayer-vietoris.json` — statement-only child, no Mathlib match.
- `citations.json` — verbatim dependency quotes for every cited proof step.

2. Attachments: none. No sorry-free slopmaster2 declaration states Tag 08DG.

3. WANTED: none; `literature/stacks-project/perfect.tex` is represented by the obtained Stacks source and Tag 08DG was checked directly.

4. The imported item had no proof. I checked the source statement against Stacks Tag 08DG and retained all clauses, including the compatibility condition for the map to E. The source proof requires three non-elementary inputs: restriction of derived direct images to nested opens, the cone triangle already supplied by the abstract derived-category definition, and the Mayer–Vietoris Hom sequence. The first and third were absent from the DAG and were added as statement-only nodes after searching the whole DAG and blueprint. The ordinary compatibility calculation on U∩V is elementary and is written as a proof step rather than a node.

## Review by M1

I read Tag 08DG (Lemma 20.45.1) and its proof, plus Tag 08BW (Lemma 20.33.3) for the Hom Mayer–Vietoris input and Tag 08BT (Lemma 20.32.8) for the open restriction/extension formalism. Step 1 uses exactly the cone-triangle clause of `def-weil-abstract-derived-category`. Step 2 uses the new restriction node for both nested-open identifications and the triangulated split-triangle consequence from the abstract derived-category node; the hypotheses are only that U and V are opens and X=U∪V. Step 3 checks the overlap equality directly from the given equation `a|_{U∩V}=b|_{U∩V}∘c`, so it is elementary. Step 4 uses exactly the first three terms of the new Mayer–Vietoris Hom node and therefore produces the required global map. I tested the construction on the one-open cases V=X and U=X, where the cone reduces to A and B respectively, and on the empty intersection, where compatibility is vacuous. Mathlib searches were run for the item and both new nodes with LeanFinder, Loogle, and grep; none states the required derived gluing results (LeanSearch was unavailable for the item and was not recorded for the children).

5. What I could not finish: nothing.

## Not duplicates

lem-sc-derived-open-restriction-pushforward vs lem-sc-derived-open-gluing: the child states the independent restriction/base-change theorem for derived direct images along nested open immersions, while the item states the resulting existence of a glued derived object and compatible global morphism.
lem-sc-derived-open-restriction-pushforward vs lem-pc-restrict-derived-direct-image-open: both derive from Tag 08FE, but the former is the unit-local two-open specialization with the canonical identity for the U pushforward stated explicitly, while the latter is the general morphism-and-open theorem in another unit.

## Second reading by M1

- Item statement: checked against Stacks Tag 08DG (Cohomology, Lemma 20.45.1), including the two-open cover, transition isomorphism, and compatible-map clause; verdict: hypotheses and conclusions agree.
- Step 1: checked against the cone construction in Tag 08DG and [def-weil-abstract-derived-category]; verdict: the distinguished cone triangle is the cited input.
- Step 2: checked against Tag 08DG and the local restriction input [lem-sc-derived-open-restriction-pushforward] (Tag 08FE); verdict: nested-open restriction identities and the split-cone restriction argument are stated explicitly.
- Step 3: checked against the compatibility equation in Tag 08DG; verdict: the two local maps are written using the restriction isomorphisms and agree on the overlap.
- Step 4: checked against Tag 08BW (Cohomology, Lemma 20.33.3); verdict: the exact Hom sequence supplies the global lift.
- New node lem-sc-derived-hom-mayer-vietoris: checked against Tag 08BW; statement is self-contained with [def-pc-derived-category], and the zero, one-open, and empty-intersection cases are consistent.
- New node lem-sc-derived-open-restriction-pushforward: checked B1-B7 against Tag 08FE and the local two-open specialization; verdict: retained as the unit-local formulation required by the route, with no Mathlib match.
- Small cases checked: U=X, V=X, U∩V=∅, and X=∅; the cone and compatibility clauses reduce as expected.
- Mathlib searches and recorded search log were checked for the item and Mayer–Vietoris child; no exact Mathlib declaration was found.

Changes: retained the unit-local restriction child to satisfy the route policy, corrected its source to Tag 08FE, expanded the split-cone and overlap-map arguments, and kept the independent Mayer–Vietoris child.
