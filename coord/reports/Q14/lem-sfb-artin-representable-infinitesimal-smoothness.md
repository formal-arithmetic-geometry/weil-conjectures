# Stage-1 report: lem-sfb-artin-representable-infinitesimal-smoothness

Group Q14, 2026-10-23. Direct delivery; only stage 1, with no Lean edits or compiles.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-artin-representable-infinitesimal-smoothness.json: item, statement unchanged, split into seven steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-limit-test-representable-property.json: statement-only, unsplit; no Mathlib match. General property test from Stacks 07WI, with precisely the Zariski-target-local and scheme-base-change hypotheses its proof uses.
- dag/nodes/sec-six-functors-basics/lem-sfb-scheme-artinian-smoothness-finite-type-tests.json: statement-only, unsplit; no Mathlib match. Stacks 02HY, implication from Artinian small-extension lifting with finite-type bottom map to smoothness.
- citations.json: all twenty-one step/node pairs, each with a verbatim statement quote.
- searches.jsonl: actual msearch.py search log. Queries recorded in the new nodes match the log. The existing item's inherited searches are retained, and fresh searches appended.

## Attachments

None. Searched the live WeilConjectures source for the exact blueprint tag and for fibred groupoids, representability, infinitesimal smoothness and Artinian smoothness. The existing SmoothArtinianLiftingAtPoint and SmoothAtPrimeArtinianLifting declarations concern scheme maps at a point, not this morphism to an arbitrary fibred groupoid, and not the finite-type-bottom-map global criterion. No complete project declaration states the item.

## WANTED

None. All sources used are in literature/stacks-project.

## Problems found and corrected

The imported node was unsplit; its statement is faithful to the specialization of artin.tex Tag 07XX. Its full lifting condition is stronger than the small-extension condition needed by that source. No hypothesis was added or removed. In particular, no descent, algebraicity, representable diagonal of the target, Rim-Schlessinger, effectivity or tangent bound is used.

The blueprint ancestor command returns None for this pre-existing chain. Retained its null from.node and its full via list, and made the exact local source places explicit for the new nodes. Read the current latest blueprint's sk-thm-sf-ctf-stability unit and direct-images proof: this remains the supporting Artin criterion on the marked-curve alteration branch of direct image (3). No unit or chapter change is proposed.

During the self-review I replaced a shorthand assertion that an affine locally finitely presented V over Spec R immediately has a global finite presentation of its coordinate ring. Step 4 now uses the cited composition law for local finite type and the elementary fact that an open containing the closed point of a local spectrum is the whole spectrum. This proves B' is a finitely generated R-algebra directly and then proves its residue field is finite type over R by taking images of generators. This avoids an unstated affine finite-presentation characterization and verifies the exact hypothesis needed to invoke the item's lifting property.

The global scheme criterion 02HY replaces only the last two sentences of 07XX's scheme argument. Its source proof is exactly the smooth-locus/finite-type-point argument invoked there, rather than an alternate route. It is a strictly smaller lemma about schemes, not a renaming of the item.

## Unfinished work

No item step is left without an argument or cited supporting statement. The two new lemmas are deliberately statement-only and remain unsplit for later stage-1 items. There are zero new Mathlib leaves. The unit's realized fields are not changed: this item is not the unit's key statement.

## Searches and duplicate audit

Read coord/delivery-errors.md B through E, both copies. Searched the entire DAG by the Stacks tags 07XX, 07XN, 07WI, 02HY, 02HX and 04AK, by label and by the statements' concepts. Ran blueprint_refs.py ancestor on the item, and search on infinitesimal smooth, limit preserving, Artinian, 07WI, 02HY, infinitesimal, smooth lifting, property limit, small extension, representable property and smooth morphisms. The blueprint has no matching lemma for either new node.

The Mathlib searches actually run with msearch.py include two semantic phrasings per new node, Loogle patterns and source grep, plus LeanSearch. All services returned successfully for the queries recorded here. Read the hits: general scheme/ring smoothness, standard smooth charts, local finite presentation, representable functors and Zariski locality do not give either the fibred-groupoid approximation test or the Artinian-restricted converse to formal smoothness. Loogle returned no hit for the specified patterns. Grep found no Artinian smoothness criterion in Mathlib/AlgebraicGeometry; the limit-property grep found only an unrelated sifted-colimit comment. Existing scheme Artinian-lifting declarations in WeilConjectures were read as well; they do not give either new statement in one line.

## Not duplicates

lem-sfb-limit-test-representable-property vs lem-sfb-limit-test-surjective-representable: the existing 07WI node proves only surjectivity on points. It cannot be applied to smoothness or to an arbitrary property P; the new node states the general property test, under explicit target-locality and base-change assumptions. The surjectivity-only node is a specialization, not a generalization that supplies this use.

lem-sfb-scheme-artinian-smoothness-finite-type-tests vs lem-weil-pbc-smooth-artinian-lifting-at-point: the existing 02HX node needs lifting for every Artinian small extension centered at the chosen point, with no finite-type restriction on the bottom map. The new 02HY node is global and requires lifting only when the bottom map is finite type. Deducing its conclusion requires the nontrivial finite-type-point detection argument, not substitution of parameters in the existing node.

lem-sfb-limit-test-representable-property vs lem-sfb-artin-representable-infinitesimal-smoothness: the new node imposes no deformation lifting and makes no smoothness assertion; it reduces tests for an abstract property to finite-presentation affine targets. The item must prove smoothness on those tests in steps 1-6.

lem-sfb-scheme-artinian-smoothness-finite-type-tests vs lem-sfb-artin-representable-infinitesimal-smoothness: the new node concerns an ordinary locally finite type scheme map over a locally Noetherian scheme. The item must construct that scheme map from a represented 2-fibre product, prove its finiteness, lift the specified isomorphism in the target groupoid and then the etale chart, and finally remove the finite-presentation base restriction.

No elementary facts were promoted to nodes: the descent of triples and arrows, verification of the residue-field hypothesis, 2-pullback lifting, and target-locality deduction stay in the item's proof.

## Review by Q14

I read artin.tex Tag 07XX (lemma-implies-smooth) and its whole proof, Tag 07XN (lemma-limit-preserving-algebraic-space), Tag 07XM (lemma-fibre-product-limit-preserving), equation-smooth and the composition/base-change deformation lemmas around it. For each new node I read its actual source: criteria.tex Tag 07WI (lemma-check-property-limit-preserving), statement and proof, and more-morphisms.tex Tag 02HY (lemma-lifting-along-artinian), statement and proof, with 02HX immediately above. For 07WI I checked that the proof uses only affine open restriction, object descent along a directed system of finitely presented affine schemes, and base change: this justifies the explicitly stated Zariski-local variant. For 02HY I checked the Noetherian and local finite type hypotheses and the finite-type condition on the bottom arrow; the source's small extensions are Artinian local with length-one kernel. The extra written square-zero description is automatic and matches the etale lifting use.

Step 1 reads pqf-def-locnoeth for the affine Noetherian base, pqf-lem-lft-fp-locnoeth for U's local finite presentation, and lem-sfb-lfp-space-scheme-limit-test for the Hom limit condition of U and V. Each cited statement has precisely that conclusion. The scheme-index systems are affine, hence quasi-compact quasi-separated, with affine transitions and the stated small directed index. U need not be separated.

Step 2 spells out the argument of 07XM rather than citing only a definition: maps to U and V descend, their isomorphism descends by full faithfulness of the target's limit equivalence, and the equality of two such isomorphisms holds at a later common stage by faithfulness. The discrete representables ensure no extra automorphism survives. I read def-trf-algebraic-space for the sheaf, representable diagonal and etale scheme atlas; lem-sfb-stack-chartwise-smooth-etale-calculus explicitly says etale implies smooth, so a space has a smooth atlas. Thus the hypotheses of lem-sfb-stack-limit-preserving-lfp apply to Z itself, without asserting the original target is a stack. Its statement supplies the necessary converse from the groupoid limit condition to local finite presentation on scheme charts.

Step 3 uses def-trf-algebraic-space to choose p, then the meaning of local finite presentation on etale scheme charts from the preceding cited result. I read lem-sfb-space-lft-cancellation: it requires local finite type only of W -> S, not of V -> S, to deduce local finite type of q. The locally Noetherian propagation sentence really appears in pqf-def-locnoeth, so it applies to V. This supplies both hypotheses of the new scheme criterion.

Step 4 uses precisely the test squares specified by the new criterion. I read clause (e) of lem-weil-pbc-proper-fp-permanence: it states composition of locally finite type maps, and does not require properness. The local-spectrum argument and reduction of generators prove finite type of l over R. The lifted triple includes the given isomorphism and restricts to the original one, as required by the item's hypothesis; it is not just an existence of an isomorphic object without compatibility. B' and B carry their R-actions through c and are local Artinian, and their residue fields are identified by the local surjection.

Step 5 uses the square-zero condition from the small-extension test, the affine first-order-thickening definition, and exactly the affine lifting assertion of lem-sfb-etale-space-infinitesimal-lifting. Its statement allows arbitrary algebraic spaces E,Y; take E=W, Y=Z, initial map b and bottom map d. Projecting pb'=d gives the required equality with c. I read spaces-more-morphisms.tex 0616/04GC against this existing node's statement.

Step 6 invokes the new scheme criterion only after all of its finiteness and test hypotheses have been verified. I read lem-sfb-scheme-etale-source-target-properties and lem-sfb-space-etale-presentation-property-criterion: the first supplies the etale-local property of smoothness, and the second says the property on one presentation covering the source holds on every presentation. The target chart is identity V, so no unproved cover of V is assumed.

Step 7 uses the explicit base-change and open-source-cover laws of lem-sfb-stack-chartwise-smooth-etale-calculus only for algebraic spaces, which are algebraic stacks. I read spaces-morphisms.tex definition-smooth and lemmas base-change-smooth and smooth-local, the source of these laws. The target-open-cover deduction is written in the step. This verifies both hypotheses on P in the new general property test. The target limit preservation in the item implies object descent, so the general test applies. No algebraicity or stack descent of the original target is invoked.

I checked small cases: R=0 forces U and all base schemes to be empty, so all lifting and smoothness assertions are vacuous; U empty also gives empty represented fibres and the empty chart; X=h_V recovers the ordinary infinitesimal criterion. No reducedness, separability of residue extensions, or Jacobson hypothesis is used. In 02HY the finite-type bottom-map restriction is essential and was retained; no use is made of the false implication that all points of a finite-type scheme over an arbitrary Noetherian ring have residue field finite type over the base. The new property test allows empty fibres and requires no quasi-compactness of them.

I checked every citation against its statement and wrote its exact statement into citations.json. Checked the dependencies for cycles back to the item; none of the reused nodes depends on it. All proof steps are under 2000 characters, the proof dependencies equal the union of uses, and both new nodes have empty proof and proof_deps. Neither is a clause or a relabelling of the item. The off-unit scheme finiteness laws and the open-immersion etaleness law are declared as generic tool uses in split_report; all algebraic-space/stack inputs are general tools, not steps of the trace formula or Poincare duality. No SGA source is used.

## Dry-run repairs

The first deliver.py --no-push exited with only two B2 wording diagnostics: the proof said “the item’s” in steps 1 and 4. Replaced them by “the assumed representability” and “the assumed lifting property”. The statements of both new nodes were already self-contained. In step 7 I additionally made the target-cover inference explicit: open inclusions T_j -> T are etale by the existing lem-weil-pbc-open-immersion-etale (whose complete statement I read), hence smooth by the cited calculus, and composition gives Z_j -> T before applying open-source locality. Added its verbatim citation, a tool-use declaration, and checked it has no dependence on this item.
