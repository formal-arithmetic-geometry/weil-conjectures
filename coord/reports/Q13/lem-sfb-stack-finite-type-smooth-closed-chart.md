# Q13 stage-1 delivery: lem-sfb-stack-finite-type-smooth-closed-chart

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-stack-finite-type-smooth-closed-chart.json`: statement node, now split into four proof steps. Mathlib verdict: no match for the algebraic-stack assertion.
- `citations.json`: 25 entries, one verbatim statement quote for each step/node citation.
- `searches.jsonl`: five fresh searches through the required msearch command, with actual service results. Both semantic phrasings, LeanSearch, Loogle and grep ran successfully. The inherited search records in the item are retained.
- `report.md`: this report. `prepare.py` is the sandbox-only preparation script, not a delivered node or library change.

New nodes: 0. New Mathlib leaves: 0. All needed inputs already have DAG nodes.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag, the item identifier, algebraic-stack terminology, finite-type points and smooth/closed chart terminology. No project declaration states the item. Mathlib's scheme results do not attach to this stack assertion.

## Wanted literature

None. Used the local Stacks sources and the current `literature/blueprint/latest/` only.

## Corrections and route

The item was unsplit, with no proof; its mathematical statement is correct and remains verbatim unchanged. Added the spectrum and residue-field definition nodes to statement dependencies. The parent route and inherited blueprint place/via chain are retained; `blueprint_refs.py ancestor` reports None, as for the live creation chain. Searches of all blueprint nodes for “finite type point”, “06FX” and “smooth chart” gave no exact duplicate. The current blueprint's `sk-thm-sf-ctf-stability-direct-images.proof.md` was read: this auxiliary pointwise groupoid chart is on its inherited alteration/moduli supporting branch of part (3), not a replacement of the unit's functor argument.

The proof follows Tag 06FX, expanding its selection of a finite type point using an etale scheme atlas of the pulled-back algebraic space, a nonempty affine open, and a maximal ideal. The scheme field-point criterion then gives a closed image after affine shrinking. The comparison of field-valued points is written out through the common field L. For Tag 06G3's last local finite type assertion, both projections of the self-relation are directly base changes of the field representative already proved locally of finite type. Its groupoid structure is provided by the existing self-relation theorem, without using that theorem's later quotient or embedding conclusions.

## Not duplicates

No new nodes were created. Reused the existing representable-diagonal, chart-test, field-point criterion and self-relation nodes. In particular no new “closed chart” or “locally finite type self-relation” node merely restates a clause of the item. The existing space finite-type point characterization was read, but is unnecessary once its point-selection argument is expanded using the already available scheme criterion.

## Review by Q13

I read the complete proof of Stacks `stacks-morphisms.tex`, Tag 06FX (`lemma-point-finite-type`), both directions, and the first proof paragraph of Tag 06G3 (`lemma-point-finite-type-monomorphism`). I also read Tag 06FZ (`lemma-identify-finite-type-points`), `morphisms.tex` Tag 01TA (`lemma-point-finite-type`), `algebra.tex` Tag 00E0 (`lemma-Zariski-topology`), and `algebraic.tex` Tags 045G (`lemma-representable-diagonal`) and 04T4 (`lemma-map-space-into-stack`), including the groupoid clause (4). The space-to-scheme compatibility is explicitly in `spaces-morphisms.tex` Tag 03MJ (`lemma-local-source-target`). There are no new-node sources to audit. The existing imported and created nodes are used only through their statements, which I opened and read in full.

Step 1 uses `def-sfb-algebraic-moduli-stack` for the representable smooth surjective scheme atlas. `def-trf-scheme-algebraic-space` allows the field spectrum to be an algebraic space, and `lem-sfb-stack-diagonal-space-source-representability` then supplies representability of its map to the stack, with no extra stack finiteness hypothesis. Its explicit scheme-base-change clause gives Z as an algebraic space. `def-trf-algebraic-space` supplies the surjective etale scheme chart E of Z. `lem-sfb-stack-chartwise-smooth-etale-calculus` states all base-change, composition, etale-to-local-finite-type and surjectivity properties taken here. `lem-sfb-space-local-properties-chart-test` explicitly says that the extended property agrees with the scheme property when both objects are schemes, so the later scheme field-point criterion really applies to h. `def-weil-affine-spectrum` states that Spec K has a point. Thus the nonemptiness argument has a nonempty target; no assumption that the whole stack or atlas is quasi-compact is used.

Step 2 uses the local affine condition of a scheme and the spectrum/residue-field definitions to introduce A and L. The nonzero ring hypothesis for `lem-weil-pbc-proper-ideal-contained-in-maximal` follows from the point in the chosen nonempty affine open, rather than being assumed. A maximal ideal gives a closed singleton by the Zariski topology, which is written out. `lem-sfb-finite-type-field-point-characterization` states exactly the equivalence with an affine neighbourhood where the image is closed and the residue extension is finite: first use it for r with extension L/L, then for f to obtain U and u. `lem-weil-pbc-open-immersion-etale` and the chartwise calculus justify the inclusion and composition between those applications. I did not use the false assertion that locally finite type morphisms always carry closed points to globally closed points. Only closedness in the resulting affine open U is needed.

Step 3 uses the open-immersion theorem and chartwise calculus for smoothness of q, not merely the definition of smoothness. The 2-fibre-product definition in `def-sfb-stable-pointed-moduli-groupoids` gives the isomorphism between the two pulled-back stack objects. `lem-weil-pbc-morphism-from-spec-field` states the full factorization of f through its canonical residue-field point, including the induced field map. `def-weil-affine-spectrum` identifies b with a field map. These produce actual representatives isomorphic over L, exactly the equivalence relation stated in the item. There is no unjustified assertion that a map factors through a locally closed subscheme merely from its set-theoretic image: factorization through the open U is literal restriction of a scheme map whose unique image point lies there.

Step 4 uses the field-point criterion with the verified closed point u and the identity extension k/k. Smoothness of q supplies local finite presentation, hence local finite type, and composition is explicitly in the chartwise calculus statement. The representable-diagonal theorem has the required diagonal hypothesis because X is an algebraic stack. `lem-sfb-self-relation-quotient-embedding` explicitly states both that R is an algebraic space and that identities, inverses and composition of isomorphisms make it a groupoid with the two projections as source and target. Only those clauses are used; no existence of an algebraic quotient is assumed. Both projections are base changes of a along a, so the already cited base-change stability applies twice, without any quasi-compactness requirement. The stronger finite-type/closed-immersion factorization in the first paragraph of 06G3 is not needed for this local finite type conclusion.

I checked B1–B9: there is no statement-only node with a concealed proof, no new undefined object or invented tag, decoded TeX has single backslashes, and no Mathlib leaf is falsely claimed. The Mathlib searches were actually run and their hits read. In particular I opened `Mathlib/AlgebraicGeometry/Morphisms/Finite.lean:222`: its closed-point equivalence requires JacobsonSpace and concerns schemes. It cannot prove this assertion for arbitrary algebraic stacks. The two semantic phrasings also returned only scheme/ring facts. No project attachment or Mathlib match was missed among these hits.

For C1–C8, every non-elementary input appears among the step's uses; every such statement was read, and all 25 citation quotes are exact substrings of those statements. No proof-internal construction of an existing node is treated as part of its interface. I searched the dependency closure of the representable-diagonal and self-relation inputs and found no path back to this item. All non-leaf statement inputs belong to the item's unit. The three off-unit inputs (maximal ideal, open immersion etale, field-morphism factorization) are already Mathlib leaves, so no additional off-unit tool declaration is necessary.

For D1–D5, the four steps carry the actual chart-selection and shrinking argument. Nothing was moved into a renamed copy of the item or a new clause node. Each non-elementary step is below 1000 characters, so no step exceeds the 2000-character long-step threshold. For E1–E7, I checked every application against its hypotheses and tested: X = Spec K; X = B G_m, where the self-relation is not asserted etale or quasi-finite; a non-Jacobson affine scheme, where closedness is obtained only after shrinking; an arbitrary non-Noetherian base; and the empty stack, which has no finite type point to start with. These checks require no stronger hypotheses and show why the locally finite type conclusion, not finite presentation or quasi-finiteness, is the right one. No statement dispute or source error was found. No SGA source or alternative purity route is used.

## Unfinished work

None in the requested one-level split. Existing dependency nodes retain their own independent work states. The required server dry run and delivery are performed after this report is written.
