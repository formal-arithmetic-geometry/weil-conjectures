# Worker report

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-fp-algebra-module-generic-freeness.json`: item, split into seven steps; no Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-pur-noetherian-algebra-module-generic-freeness.json`: one new statement-only lemma, Stacks Tag 051R; unsplit, no Mathlib match.
- `citations.json`: every step citation backed by the full verbatim statement of the cited node.

## Attachments

None. Searched the slopmaster2 project for the item id, generic freeness/flatness, genericFreeness, and the Noetherian source label. Read `WeilConjectures/Mathlib/RingTheory/Spectrum/Prime/FreeLocus.lean`: `Module.Finite.exists_free_localizedModule_powers_of_isDomain` (line 123) assumes the module finite over the base domain; `Module.exists_flat_localizedModule_powers` (line 543) only concludes flatness. Neither states the item or the new lemma. The upstream master checkout was read-only reference material, never evidence of finished proofs.

## WANTED

None; both source proofs are present in `literature/stacks-project/algebra.tex`.

## Findings and changes

The item's statement matches Tag 051S, `algebra-lemma-generic-flatness-finitely-presented`: the base is a domain, not assumed Noetherian; both the algebra and its module are finitely presented; the conclusion permits an infinite basis. No statement correction was needed. The imported empty proof has been replaced by the finite-coefficient-subring argument in the source. Neither the module's finite presentation over the algebra nor its finite generation implies finite presentation over the base. I therefore rejected the apparent Mathlib hit `Module.FinitePresentation.exists_free_localizedModule_powers` after reading its base-finite-presentation hypothesis at `Mathlib/RingTheory/Localization/Free.lean:78-91`. PID freeness results also assume the wrong base and finiteness.

Read the chapter `sec-smooth-purity`, unit `sk-prop-sf-cbc`, and the ancestor blueprint `lem-fin-generic-radicial-smoothing.md`. This is a lower-level algebra ingredient in the existing shrinking/finite-presentation preparation; no unit or chapter route changes. The item's `blueprint.from.place` already identifies the Tag 051S ingredient under Tag 051T. The new node identifies that same place and the Noetherian input inside Tag 051S, with the item added to `via`.

## Not duplicates

lem-pur-noetherian-algebra-module-generic-freeness vs lem-sbc-finite-type-algebra-generic-flatness: the existing node, whose source mentions 051R, only gives generic flatness of the algebra itself; the new node gives generic freeness of every finite module over a finite-type algebra, assuming a Noetherian domain base. Flatness does not assert freeness or cover the arbitrary module.

The new lemma is not a clause renamed from the item: it is the preceding Noetherian finite-type/finite-module theorem, with no finite-presentation hypotheses on its algebra or module. The substantive reduction from the item's arbitrary domain to that theorem is carried by steps 1–3, and the passage back to the original localized module is carried by steps 5–7.

Before creating it, searched the DAG for `051R`, `lemma-generic-flatness-Noetherian`, generic freeness, generic-flatness and Noetherian coefficient-subring terms. Opened the existing generic-flatness node above, the item's parent, the existing Noetherian algebra permanence lemma, and the scalar-extension universal property. Whole-blueprint searches for `051R`, `051S`, `generic freeness`, `generic flatness`, `Noetherian generic`, `finite type algebra`, `free module`, and `extension of scalars` gave no existing blueprint statement of this result. `blueprint_refs.py ancestor` returned `lem-fin-generic-radicial-smoothing`. No new definition was needed: finite type and free are explained in the new statement, and Noetherian, finite module and ring localization cite existing definition nodes.

## Unfinished work

Only the single new unsplit node remains for a later stage-1 worker. Its proof is not included in its statement or node: the source Tag 051R has the prime filtration/relative Noether normalization/dimension induction argument, which will be its worker's task. There is no other deferred ingredient in the item's seven steps.

## Review by NR

I read Tag 051S and the entire preceding Tag 051R statement and proof in `algebra.tex`, along with Tag 00FN (`algebra-lemma-Noetherian-permanence`). I checked the item hypothesis by hypothesis against 051S and the new lemma against 051R. The latter explicitly includes the Noetherian hypothesis which cannot be assumed on the original base. The new node has a complete statement introducing both rings and the module, empty proof and proof dependencies, a Stacks tag with the local TeX label, and inherited chapter/unit. Its Mathlib search records come from the actual msearch log, including the LeanSearch HTTP error as unavailable. Two semantic phrasings and two source-grep phrasings found no match. Loogle on `Module.Free, Algebra.FiniteType` returned no hits. The module localization theorem was read and rejected for the precise finiteness mismatch, not by its name. No Mathlib leaf was created.

For step 1 I opened `def-sc-finitely-presented-module`: it gives exactly the finite-free presentation used. The two successive quotients merely write that presentation over the polynomial ring, with all algebra relations acting on every coordinate. The zero-generator and zero-relation cases are included.

For step 2 I opened `lem-weil-pbc-finite-type-algebra-noetherian`: its statement covers any finite-type algebra over a Noetherian base, so applies to the coefficient subring as a finite-type Z-algebra. I supplied the elementary division-with-remainder proof that Z is Noetherian, rather than hiding another theorem. The coefficient subring is unital and actually inside R, hence a nonzero domain even in positive characteristic. Its algebra B0 and module M0 are actual presentation constructions. No assumption that R is flat over R0 appears.

For step 3 I opened `lem-weil-pbc-module-base-change-universal-property`: it gives the scalar-extension Hom bijection and the pure-tensor formula used, rather than a theorem about exactness. The rest is an elementary comparison of the two presentation relations: all monomial coordinate vectors have identical relations over R0 and R, because the coefficients were included in R0; polynomial multiples are sums of monomial multiples. This supplies both inverse identities and does not appeal to tensor exactness, a hidden descent theorem, or the proof of another node.

Step 4 uses the exact statement of the new 051R node. Step 2 supplied Noetherian R0, its domain property, the finite-type algebra B0 and finite B0-module M0. The nonzero element stays nonzero under the coefficient inclusion. This is the non-elementary generic-freeness input, rather than a claim that the conclusion follows from flatness.

For steps 5 and 6 I again checked the scalar-extension universal-property node and opened `def-weil-ring-localization-away`. The latter supplies the fraction equality and arithmetic formulas. The maps are displayed, and annihilating powers become units only in Ra, where they should. Both inverses are checked on fractions or pure tensors. The comparison with (R0)a uses its own coefficient-inclusion fraction map. These two elementary steps prove the localization and iterated scalar-extension identifications rather than just saying they commute or clearing unspecified denominators.

For step 7 the same scalar-extension statement gives the linear extension. The finite-support coordinate formula and its inverse prove freeness directly, including an infinite basis and the empty basis; no theorem asserting finite rank or a tensor-preserves-direct-sums lemma is smuggled in.

Small cases checked: L=0 gives the empty basis; A=R[x], L=A gives the necessarily allowed infinite monomial basis; n=m=0 gives a finite presentation over R; empty coefficient set gives the prime subring, finite type over Z and a domain; characteristic p works because the inclusion R0 into R is injective even though Z into R0 is not; the zero algebra and t=0 present the zero module. The Noetherian new lemma allows B=0 and M=0, with a=1. The item requires a domain, so the zero base ring is excluded. I corrected no source statement and added no hypotheses. Checked delivery-errors B–E against these statements and maps: the only new node is a genuine cited ingredient, every cited fact is in the quoted statement, and the elementary steps give their arguments instead of relying on source tags as black boxes.


## Second reading by NR

- Item statement: compared all three hypotheses and the unrestricted-rank freeness conclusion with Tag 051S, algebra-lemma-generic-flatness-finitely-presented; exact agreement, including non-Noetherian domains.
- Step 1: opened def-sc-finitely-presented-module and checked the two quotient presentations against 051S; the lifts and the vectors g_j e_k give precisely the stated relations, including t=0 and n=m=0. Pass.
- Step 2: opened lem-weil-pbc-finite-type-algebra-noetherian and def-weil-pbc-noetherian-ring against Tag 00FN, algebra-lemma-Noetherian-permanence; Z is Noetherian by the displayed ideal argument, and the unital coefficient subring is a domain even in positive characteristic. B0 is finite type and M0 is generated by t vectors. Pass.
- Step 3: opened lem-weil-pbc-module-base-change-universal-property; its Hom bijection plus the monomial-coordinate presentation identifies exactly the maps to each R-module N. Taking the indicated two N gives both inverse identities. No tensor exactness or flat coefficient inclusion is assumed. Pass.
- Step 4: compared the cited new node with Tag 051R, algebra-lemma-generic-flatness-Noetherian; all four hypotheses were established in step 2 and inclusion preserves a nonzero a. Pass.
- Step 5: opened the scalar-extension node and def-weil-ring-localization-away; the annihilating-power relation becomes equality in H because a is invertible. Checked both composites on fractions and pure tensors. Made the intermediate map to H explicit, so the inverse is typed throughout. Pass after clarification.
- Step 6: checked both displayed maps using the same two cited statements. For the inverse, the relation a^u(a^k v-a^j v')=0 becomes equality after multiplying by the invertible a^{-u-j-k}; moving c/a^k across a tensor gives r c/a^{k+j} on both sides. For the forward map, c in R0 moves across by the tensor relation. The composites fix r tensor v and r tensor (v/a^j). Pass.
- Step 7: checked the scalar-extension Hom bijection and the two finite-support formulas; balancing moves each coefficient c_i across the tensor, and the composites fix pure tensors and coordinate vectors. Works for infinite I and I empty. Pass.
- New node lem-pur-noetherian-algebra-module-generic-freeness: read the complete 051R statement and proof. Its Noetherian/domain/finite-type/finite-module hypotheses and free localized conclusion agree exactly; B=0 or M=0 permits a=1, and a field base permits an infinite-dimensional vector-space basis. Statement-only, empty proof/dependencies, all introduced objects and non-basic notions defined inline or by the three opened definition nodes; correct source tag/label. Repaired malformed prime notation. Pass B1-B7.
- New-node necessity: searched the full DAG for 051R and generic freeness, opened lem-sbc-finite-type-algebra-generic-flatness (only algebra flatness) and lem-sbc-generic-flatness (scheme flatness); neither gives module freeness. Whole-blueprint searches for generic freeness and 051R returned zero nodes; ancestor is lem-fin-generic-radicial-smoothing, whose proof was opened. The Noetherian input is neither elementary nor a renamed clause: steps 1-3 perform the essential descent from an arbitrary domain, and steps 5-7 perform the return. Retain one unsplit node.
- Independent Mathlib check: ran msearch with a polynomial-algebra basis phrasing, Loogle Module.Free, IsNoetherianRing, and grep for basis/localization and genericFreeness. Read Localization/Free.lean:41-49,78-91 and the source FreeLocus.lean:123,543. The basis/localization declarations require base-finite presentation or an already existing basis; source finite-module generic freeness requires base-finiteness, while source algebra-module generic flatness concludes only flatness. No exact leaf; actual searches appended to both nodes and retained in searches.jsonl.

Changes: corrected m\prime and ell\prime to primed variables in the new statement, its citation, and step 5; specified the intermediate scalar-extension map in step 5's inverse; recorded the three independent searches. No hypotheses, conclusions, proof route, or node count changed. The original Review by NR remains above.

Cross-unit tools: lem-weil-pbc-finite-type-algebra-noetherian supplies Hilbert basis/permanence and lem-weil-pbc-module-base-change-universal-property supplies the tensor Hom bijection; these are general algebra tools, not replacements for a unit-level step. No node of this unit supplies those statements. Their use is reported for the maintainer's tool-use decision; no tool_uses entries were added.

Delivery command syntax: the brief's trailing dot is rejected by deliver.py's two-positional-argument parser. Use its documented invocation without the dot for both dry run and push; no script was modified.
