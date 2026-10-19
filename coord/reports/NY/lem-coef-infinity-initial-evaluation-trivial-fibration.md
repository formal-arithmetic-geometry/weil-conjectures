# Stage-1 worker report

1. Files written:

- `dag/nodes/sec-six-functors/lem-coef-infinity-initial-evaluation-trivial-fibration.json` — split statement with four proof steps.
- `dag/nodes/sec-six-functors/lem-coef-infinity-initial-object-left-anodyne.json` — statement-only lemma; Mathlib searches found no match.
- `dag/nodes/sec-six-functors/lem-coef-infinity-left-anodyne-restriction.json` — statement-only lemma; Mathlib searches found no match.
- `citations.json` — verbatim statement quotes for every proof-step citation.

2. Attachments: none.

3. WANTED:

- Kerodon Corollary 4.7.3.22 (tag 02J5), the initial-object/left-anodyne implication, for `lem-coef-infinity-initial-object-left-anodyne`.
- Kerodon Proposition 4.2.5.4 (tag 0154), the left-fibration/left-anodyne exponentiation theorem, for `lem-coef-infinity-left-anodyne-restriction`.
- Kerodon Proposition 5.6.6.19 (tag 038R), implication (2) => (3), for the item.

4. What was checked and corrected:

The item has no finished declaration in either source checkout, so it is not an attachment. I read the item node, its chapter `sec-six-functors`, its unit `sk-prop-sf-biduality-general`, and the ancestor `prop-coef-integral-exceptional-adjoint`. The source is Kerodon 038R: condition (2) is exactly that the chosen object is initial, and condition (3) is the stated evaluation trivial Kan fibration. I searched the whole DAG and both blueprint snapshots for the item, for initial-object left-anodyne inclusions, and for left-anodyne restriction into left fibrations; no existing node states either supporting lemma. I also checked the source tree for the blueprint tag and declaration name; there is no Lean declaration for this item.

The first new node records the precise initial-object implication from Kerodon 02J5, with the left-anodyne class defined in the statement. The second records Kerodon 0154's full restriction map, including its base-map fiber product and the trivial Kan conclusion. Neither is a restatement of the item's evaluation clause: they are reusable general lemmas, and the item specializes them to the singleton inclusion and then takes a fiber over the fixed map (p:D\to B).

For step 1 I checked that the item hypotheses give a quasicategory (D) and an initial (d), exactly the hypotheses of the first new node. For step 2 I checked that (q:T\to B) is a left fibration and that the inclusion from step 1 is left anodyne, exactly the hypotheses of the second new node. For step 3 I unpacked the degreewise internal-functor definition: the fiber of the restriction theorem over (p) is the simplicial set of maps (H:D\times\Delta^n\to T) satisfying (qH=p\operatorname{pr}_D), and its target fiber is (T\times_B\{p(d)\}=T_b); restriction is therefore the displayed evaluation map. Pulling back each boundary lifting square preserves the lifting property. Step 4 simply unfolds the project's definition of trivial Kan fibration, including (n=0) vertex surjectivity.

I tested edge cases while checking the specialization: (D=B=\Delta^0), (D=\Delta^1) with initial vertex (0), empty (T) and (T_b), and empty base. These agree with the statement: the empty target fiber gives an empty source fiber, and the (n=0) clause is vacuous when the target is empty. The recorded searches were rerun with each node's own id; Mathlib has only ordinary model-category/Quillen declarations and no left-anodyne or quasicategorical initial-object theorem.

## Review by NY

I read the current item and every cited node in full. The item source and the two supporting sources were checked online, and all three are recorded as WANTED because no archival copies are present under `literature/`. I verified that the item keeps the exact hypotheses and conclusion, including the fixed universe, both left fibrations, the strict base equation, the fiber (T_b), empty cases, and the boundary (n=0) clause. I checked every proof dependency against the cited statement: step 1 uses only the first new lemma; step 2 uses only the second; step 3 uses the second lemma, the internal-functor definition, and the boundary-lifting definition; step 4 uses the boundary-lifting definition. The quotes in `citations.json` are verbatim substrings of those statements. I checked that the support nodes are strictly more general than the item's specialization, that no duplicate or cycle is introduced, and that the blueprint ancestry points to the specified paragraph of `prop-coef-integral-exceptional-adjoint`. The item statement was not weakened or changed.

## Not duplicates

lem-coef-infinity-initial-object-left-anodyne vs lem-coef-infinity-terminal-anodyne: the existing node characterizes right-anodyne inclusions of a terminal vertex via contractibility of maps into that vertex; the new node is the opposite left-anodyne assertion for an initial vertex and uses the opposite horn orientation.

lem-coef-infinity-initial-object-left-anodyne vs lem-coef-relative-limit-initial-components: the existing node reduces relative limits over a disjoint union using initial objects and cites 02J5 only as an auxiliary cofinality fact; it does not state any left-anodyne inclusion theorem.

lem-coef-infinity-left-anodyne-restriction vs lem-coef-infinity-right-fibration-exponentiation: the existing node is the right-fibration/right-anodyne exponential lifting theorem, while the new node is its left-fibration/left-anodyne dual, with opposite horn orientations and no quasicategory restriction in the cited right-fibration statement.

5. What could not be finished:

No archival Kerodon source is available locally, and Mathlib has no matching declarations; the proof therefore remains a natural-language split with the three WANTED source entries above.


## Second reading by NY

This section supersedes the earlier proposed helper-node list and the earlier "Not duplicates" conclusions; the worker's sections above are preserved. I read all three sandbox nodes, their sources online, every statement cited by the repaired proof, the unit and chapter records, and paragraph 2 of `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md` (the first/last derived Hom comparisons). The inherited unit and blueprint ancestry are unchanged.

- Item statement: compared every hypothesis and conclusion with [Kerodon 038R, Proposition 5.6.6.19, (2) => (3)](https://kerodon.net/tag/038R): one fixed universe, both left fibrations over the same quasicategory, the initial vertex, strict maps over the base, the target fiber, vertex surjectivity, and all boundary dimensions agree; verdict: unchanged and correct.
- Step 1: opened clause (4) of `lem-coef-infinity-relative-cone-equivalence`, `def-cbc-enhanced-diagrams-cones`, and `lem-coef-infinity-terminal-anodyne`; the first supplies both the quasicategory opposite and the required right-pinched mapping-space comparison, the definition supplies contractibility out of the initial object, and the last applies to precisely those mapping spaces in $D^{\mathrm{op}}$; verdict: valid. Read [02J5, Corollary 4.7.3.22, (1) => (3)](https://kerodon.net/tag/02J5) and [01L5, Proposition 4.6.5.10](https://kerodon.net/tag/01L5) for the pinch convention. This avoids assuming that reversal identifies the two right-pinched models by definition.
- Step 2: opened `def-coef-infinity-fibrations` and `lem-coef-infinity-right-fibration-exponentiation`; reversal changes horn index $k$ to $n-k$, including $n=1$, so the given left-fibration hypothesis supplies exactly the required right-fibration hypothesis on $q^{\mathrm{op}}$; the existing theorem's full relative pullback target and trivial Kan conclusion match [0154, Proposition 4.2.5.4](https://kerodon.net/tag/0154); verdict: valid, with no missing quasicategory or nonemptiness condition.
- Step 3: checked against the degreewise internal-functor definition and `def-weil-pbc-trivial-kan-fibration`; the formula $\beta(a)\mapsto n-\beta(m-a)$ is involutive, agrees with the reversed simplex operators, commutes with restriction and postcomposition, and preserves non-surjectivity defining boundaries; verdict: elementary. Reversing a boundary square, filling it, and reversing the filler proves the required lifting statement explicitly; dimension zero gives the vertex clause.
- Step 4: checked against both definitions cited in this step; the pullback along $t\mapsto(p\operatorname{pr}_D,t)$ has exactly $qH=p\operatorname{pr}_D$ and $H|_d=t$ in every degree. A filler for the composite square satisfies those two equalities, including for a vertex lift; verdict: elementary. Read Stacks tag 08NL, `simplicial.tex`, label `definition-trivial-kan`, for the separate vertex and positive-dimensional clauses.
- Proposed new node `lem-coef-infinity-initial-object-left-anodyne`: its hypotheses, left-horn range, and initial-object dual conclusion agree with 02J5; its statement-only form and definition references were checked. Verdict: REMOVE, since clause (4) of the existing relative-cone-equivalence node and the existing terminal-anodyne node give it directly. Step 1 now writes this argument and cites both existing statements.
- Proposed new node `lem-coef-infinity-left-anodyne-restriction`: its complete relative pullback formula and left-fibration/left-anodyne hypotheses agree with 0154; its statement-only form and definition references were checked. Verdict: REMOVE, since order reversal and the existing right-fibration-exponentiation theorem supply precisely the result needed here. Steps 2 and 3 write the horn, internal-functor, and boundary arguments instead of creating a dual theorem node.

Independent searches: ran `msearch.py` for this item with LeanFinder queries "Simplicial sets one sided anodyne extensions and restriction of internal hom along an initial vertex" and "Relative internal hom of simplicial sets has boundary lifting against a one sided horn fibration and an anodyne cofibration", Loogle `"anodyne"`, and grep `leftAnodyne|rightAnodyne|initial.*[Vv]ertex|[Vv]ertex.*initial`. Actual responses are preserved in `searches.jsonl` and the item's search records. Read Mathlib `SimplicialSet/CategoryWithFibrations.lean:35-103`, `SimplicialSet/AnodyneExtensions/Basic.lean:66-91`, and `Quasicategory/Basic.lean:32-64`: these give all-horn Kan-Quillen fibrations, ordinary anodyne extensions, and inner horn filling, respectively, rather than either proposed one-sided result. No Mathlib leaf is justified. Whole-DAG tag/key-word searches found the three existing lemmas now cited; whole-blueprint searches in both snapshots found no imported evaluation theorem. Read-only searches of both source checkouts by item/helper names and left-anodyne vocabulary found no finished attachment.

Edge cases: for $D=B=\Delta^0$, evaluation is the identity on $T$; for $D=B=\Delta^1$, $d=0$, $p=\mathrm{id}$, the opposite calculation uses the final vertex in the reversed interval and has the correct horn orientation. If $T_b$ is empty, a map from nonempty $D$ over the base would yield a point over $b$, so the source is empty too. If $T$ is empty this applies immediately. An empty base admits no datum $d\in D$, so the hypotheses are impossible. The $n=0$ boundary is empty, and $n=1$ reversal interchanges its two vertices; both are explicitly covered. No scheme/ring or coefficient assumptions enter this simplicial assertion.

Changes made:

- Dropped both uncommitted supporting nodes as unnecessary consequences of existing same-unit statements, leaving **0 new nodes and 0 Mathlib leaves**.
- Replaced steps 1 and 2 by applications of those existing statements, and wrote the reversal and strict pullback arguments in steps 3 and 4. This also removes the original JSON strings' accidental tab/carriage-return escapes in TeX commands.
- Regenerated `citations.json` with one full verbatim statement quote for each of the nine final step citations, and made `proof_deps` exactly the union of the step citations.
- Preserved the item statement and its original Q113 `created` provenance, checked byte-for-byte against the shared node. The creator identifies the earlier delivery which introduced this now-existing item; it is not this split's author field.
- Recorded the independent Mathlib searches and replaced the split summary/proof provenance to describe the final argument. All three proof lemmas are in `sk-prop-sf-biduality-general`; no new tool-use record or route change is needed. An independent dependency traversal found no path from any of them back to the item.

