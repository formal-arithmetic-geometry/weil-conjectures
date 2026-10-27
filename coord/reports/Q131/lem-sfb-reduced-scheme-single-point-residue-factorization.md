# Q131 stage-1 report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-reduced-scheme-single-point-residue-factorization.json`: statement item, now split into six steps. The statement and statement dependencies are unchanged. Mathlib verdict: no single exact declaration for the item; the construction requires the vanishing and unit arguments before the existing residue-field lifting theorem applies.
- `citations.json`: verbatim statement quotations for every node cited in every step.
- `searches.jsonl`: actual msearch queries and result digests. Earlier output was read and reused on resumption; the queries were not rerun merely because the launcher paused the session.
- `report.md`: this report.

No new nodes; zero new Mathlib leaves. The proof reuses existing Mathlib leaves and the existing closed node `lem-weil-pbc-spec-field-point-residue-field`.

## Attachments

None for the item. Searches of `lean/WeilConjectures/` by the exact blueprint tag and by reduced/singleton/residue-factorization terminology found no finished declaration covering arbitrary reduced scheme sources. In particular `AlgebraicGeometry.spec_field_point_residue_field_affine_open` in `WeilConjectures/AlgebraicGeometry/SpecFieldPointResidueField.lean:62` computes the canonical point's restriction to an affine neighbourhood; it does not assert our reduced-source factorization. Its existing DAG node is cited in step 4, rather than claiming it as an attachment for this item.

## WANTED

None. All sources used are present in the read clone.

## Findings and corrections

Stacks Tag 0H1M, `morphisms.tex`, `lemma-factor-through-point` at lines 15600 onward, states exactly the item, and explicitly omits the proof. Its affine-ring hint assumes a unique point in the image, which only covers nonempty affine sources. I used containment in the singleton throughout, so the zero ring and the empty scheme are covered as the item requires. This is an expansion of the hint, not a statement correction or a source dispute. Accordingly `proof_origin.by` is `agent`.

The source's omitted affine-local reduction also needs compatibility on intersections. I give this in step 5 using arbitrary affine refinements and the residue-field uniqueness clause, rather than assuming affine intersections or quasi-separatedness. The only quasi-compact objects used are individual affine opens in step 2.

I initially wrote the localization and quotient construction out using the existing localization universal property. While checking the exact canonical-point computation in the existing Lean file, I found `lem-weil-pbc-prime-residue-field-algebra`, whose clauses (c) and (d) already state the required uniqueness and existence for arbitrary commutative codomains. I replaced the inline construction with this node, and used clause (2) of `lem-weil-pbc-spec-field-point-residue-field` for the canonical map into X. This removes an unnecessary repeat of existing work and makes the canonical-map identification an exact statement citation.

The blueprint search (`blueprint_refs.py search` for residue field, single point, factor through, and unit if), whole-DAG keyword/tag searches, and the existing residue-field nodes were checked. No blueprint node states this item in another form. `blueprint_refs.py ancestor` reports a null ancestor in the inherited created-item chain; I retained the inherited `from.node`, full place and via chain rather than inventing an ancestor. I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and its direct-images proof. This scheme lemma is an inherited supporting prerequisite far below its direct-image clause, not a change to the unit route or the chapter. The worker does not own the unit's key statement and has not edited its realization fields.

## Unfinished work

None for the one-level split. No new unsplit subproblems were needed. No Lean files were written and no compiler, Lake, local DAG check or local preflight was run. The required checks are performed on the server through the supplied tools.

## Not duplicates

No new nodes were created. Existing nodes reused include the affine-open stalk computation, affine quasi-compactness, nilpotence of a section vanishing at every point, the basic-open unit criterion, prime-residue-field lifting and uniqueness, the canonical affine residue-point computation, and scheme morphism gluing.

## Review by Q131

I read the actual statement and omitted-proof hint of Stacks 0H1M, not just a tag summary. The proof below supplies the hint's missing ring argument and the passage back from affine sources to arbitrary schemes. For the residue field, I also read `algebra.tex`'s local-ring discussion and localization universal property, the source of the existing prime-residue-field node, and the Mathlib definitions and lemmas in `RingTheory/LocalRing/ResidueField/Ideal.lean` (lift, lift_algebraMap and ringHom_ext). The two key lifting hypotheses are established separately in steps 2 and 3; the lifting theorem alone is not a one-line specialization proving the whole item.

For step 1, I opened `def-pc-scheme`, `def-weil-locally-ringed-space-morphism`, `lem-weil-pbc-affine-open-spec-points`, `lem-weil-pbc-affine-open-stalk-localization`, `def-weil-pbc-localization-at-prime`, `def-weil-residue-field`, `def-pc-reduced-scheme` and `def-weil-affine-spectrum`. They supply exactly the affine points, stalk localization compatible with germs, maximal ideal, residue quotient, reduced sections and contravariant ring map that the step takes from them. Factoring f into its open target is spelled out on sheaf maps; it is a restriction of the given morphism. The local stalk condition is inherited, so no extra factorization theorem or closed-image assertion is assumed. I read Schemes 01I1 (`lemma-morphism-into-affine`) and the open-subspace/open-immersion discussion as well.

For step 2, the cited affine-stalk statement puts a in p precisely into the maximal ideal at x. The cited definition of a locally ringed morphism says the stalk maps are local, and its restriction-compatible sheaf maps give compatibility with germs. The cited residue-field definition identifies zero value with membership in that maximal ideal. I opened the two further nodes: affine-scheme-qcqs explicitly supplies quasi-compactness, and qc-scheme-vanishing-section-nilpotent requires precisely quasi-compactness and zero residue values. I read the relevant 03GY paragraph in `more-morphisms.tex` (around lines 15135--15143). Applying it only to V_i checks its hypothesis without imposing quasi-compactness on Y. The reduced-scheme definition explicitly says sections on every open are reduced, which kills the resulting nilpotent.

For step 3, I checked that the cited stalk-localization and localization-at-prime statements supply both the units outside p and the description of the maximal ideal at each prime of Spec B_i. Preserving units is immediate for a ring map. The node `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact` explicitly states in clause (ii) that D(b) is the whole spectrum iff b is a unit. I read Algebra Tag 00E0 (`lemma-Zariski-topology`), including the proof that D(b)=Spec B implies bB=B. No global-sections unit criterion for a general scheme has been silently substituted.

For step 4, I opened `lem-weil-pbc-prime-residue-field-algebra` and checked clause (d) literally: p is killed, its complement goes to units, and the codomain is any ring S. Thus it applies to each B_i, not just to fields, and includes the zero ring. I opened `lem-weil-pbc-spec-field-point-residue-field`; clause (2) gives precisely the identification and canonical residue-point factorization used here. I read its finished Lean affine-open declaration and proof at lines 62--83. The contravariant composition formula then gives the asserted composite ring map, and the affine-spectrum definition supplies full faithfulness. This is why the final draft cites the canonical affine-point lemma rather than taking an unstated compatibility from a definition node.

For step 5, clause (c) of the prime-residue-field algebra node explicitly allows any codomain C and equality after precomposing with A; it says exactly what is needed for restrictions to any affine open W of the overlap. The scheme definition permits affine neighbourhoods at every point. The affine-spectrum node translates equality of ring maps to equality of morphisms, and the opened scheme-morphism-gluing node explicitly includes equality of maps on an arbitrary open cover. I never assert that V_i intersect V_j is affine or quasi-compact.

For step 6, that same gluing node supplies existence for a compatible family on any open cover and uniqueness/equality after restriction. It has no finiteness or nonemptiness hypothesis on its index set. The empty-cover instance therefore gives the unique empty-source morphism and its composite equality. No uniqueness or monomorphism assertion about residue points is needed here beyond the explicitly cited ring-map uniqueness in step 5.

I checked the small cases explicitly. For Y empty, all local conditions are vacuous and the empty-cover gluing argument applies. For an empty affine chart, B_i is the zero ring: its spectrum is empty, nilpotence causes no problem, and its only element is a unit, so the residue-field lift to that ring exists. For X=Spec k[t], x=(0), and Y an infinite disjoint union of Spec k(t), the point is nonclosed and Y is not quasi-compact, yet every step applies. For non-affine overlaps, step 5 uses further affine covers. No nonempty, Noetherian, finite type, separated, or quasi-separated hypothesis is used. Reducedness is essential: the identity of Spec k[e]/(e^2) has singleton topological image but cannot factor through Spec k, because such a factorization would send e to zero rather than e. Our proof invokes reducedness precisely where that example fails.

Against delivery-errors B1--B10: there are no new statements to duplicate or leave unsearched; all cited notions have their actual definition nodes, sources use verified tags/labels, TeX in the new proof text has one backslash after JSON decoding, inherited fields are preserved, and no finished whole-item declaration was found. Mathlib search entries added here are actual msearch queries in searches.jsonl; pre-existing entries are retained as inherited records.

Against C1--C8: every non-elementary input is an existing cited statement whose statement I opened, and citations.json quotes it verbatim. The only inline arguments are restrictions of sheaf maps, preservation of units, equality of induced ring maps, and assembly on covers. I do not take a theorem from the proof of a cited node. The cited tools are Mathlib leaves or a node recorded closed, and do not replace the unit's route. The server DAG check found no cycle or other introduced finding.

Against D1--D5: the six steps actually derive the conclusion; no clause or the whole item is exported to a renamed new node. The source's omitted argument is supplied, and no induction or mutually dependent construction is used. All proof steps are shorter than 2000 characters (the longest is 784), and none hides a comparison lemma: the canonical-point comparison and residue-field universal property are existing statements cited directly.

Against E1--E7: the hypotheses used in each cited result were checked above, including the affine-only quasi-compactness and arbitrary-ring codomains. Objects and variance match: h_i goes from V_i to Spec kappa(x), and its composite with i_x goes to X. The proof constructs the scheme factorization, not just its point map. The map on A is explicitly lambda_i composed with pi; equality on overlaps is justified by the ring-map uniqueness clause, not by the assertion that the underlying point maps agree. There is no source statement error or ambiguity of coefficient categories here.
