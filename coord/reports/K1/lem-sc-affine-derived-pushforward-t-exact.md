1. Files written:
- `dag/nodes/sec-picard-framework/lem-sc-affine-derived-pushforward-t-exact.json`: item, split proof, no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-affine-derived-cohomology.json`: statement-only node, no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-affine-derived-pushforward-conservative.json`: statement-only node, no Mathlib match.
- `citations.json`: verbatim statement quotes for every step citation.

2. Attachments: none. I searched the slopmaster2 source for the item id, blueprint tag, affine derived-pushforward terms, and likely theorem names; no sorry-free exact declaration exists.

3. WANTED: `literature/stacks-project/perfect.tex`, Tags 0AVW and 08I8, for the affine derived equivalence and conservativity inputs.

4. The imported item had no proof. I split the proof into the cohomology comparison, the t-structure bound argument, and reflection of isomorphisms. The two auxiliary nodes are strictly smaller statement-only inputs and are not relabellings of the item. Mathlib searches were run for both new nodes with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and recorded as unavailable.

## Review by K1

I read the item and its ancestor `lem-sc-finite-duality`, plus the source labels for Stacks Tags 0AVW and 08I8. The item statement retains exactly the affine morphism, schemes, quasi-coherent derived categories, standard t-structures, and isomorphism-reflection claims. The cohomology node states the precise equality used in Step 1, including quasi-coherence of the pushforward cohomology. The conservative node states exactly the implication used in Steps 2 and 3. The standard t-structure definition node supplies the meaning of the upper and lower bounds.

Step 1 uses only the cohomology node, and its quoted sentence gives the displayed comparison verbatim. Step 2 uses that comparison, the conservative implication, and the standard t-structure definition; vanishing of each cohomology sheaf is the only inference beyond those statements. Step 3 directly applies the conservative node to the given morphism. All non-elementary uses are cited and no step relies on a node's proof.

I checked the hypotheses in the affine identity example $f=\mathrm{id}$ and for $X=\operatorname{Spec}(A)\to\operatorname{Spec}(B)$, where the comparison is restriction of cohomology modules; the zero complex tests both bounds and conservativity. The new statements are self-contained, use doubled TeX backslashes in JSON, have blueprint references from `lem-sc-finite-duality`, and carry only statements because they are unsplit. No source or statement error was found.

5. Nothing remains unfinished in the split.
