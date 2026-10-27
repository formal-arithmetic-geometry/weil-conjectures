# Q45 stage-1 delivery: lem-sfb-group-dilatation-universal-property

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-group-dilatation-universal-property.json — split the existing statement into eight proof steps; Mathlib verdict: no match for the item.
- citations.json — one verbatim statement quotation for each of the 34 step citations.
- searches.jsonl — actual searches recorded by the required msearch.py command. The inherited item searches remain intact; current searches and their genuine returned records were appended.
- report.md — this review.

No new DAG nodes and no new Mathlib leaves. The sandbox also contains write_split.py, an item-local drafting script; it is not a delivered node or a change to any launcher script.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for dilatation and Neron blowup terminology; no declaration states the item. Read WeilConjectures/Blowup/Affine/ChartAlgebra.lean: it provides the existing normal-form and fraction-equality nodes used below, not the whole group dilatation theorem. Its other chart maps are not mistaken for a universal lifting property into a ring where pi is not invertible.

## WANTED

WANTED: local archive of Bosch–Lütkebohmert–Raynaud, Néron Models, §3.2, printed pp.62–64, for lem-sfb-group-dilatation-universal-property. The repository has no BLR PDF. Read the primary-source scan already named by the item's source, https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf, PDF pages 68–70, including the construction, Proposition 1 and Proposition 2(d). No download or modification of literature was made. The agent-written globalization is marked proof_origin.by = agent; it follows this read construction rather than claiming a local source file exists.

## Problems found and corrected

The statement is sound and unchanged. It was statement-only. The important potential proof gap is that a universal property only on smooth test schemes would not construct multiplication on a merely flat G'. The proof establishes the stronger flat-test property from the ring calculation first. It also proves the locally finite type globalization without assuming a finite affine cover of G or a quasi-compact centre F. One cannot extend A[1/pi] to a test ring C where pi is not invertible: step 2 instead defines images of fractions using unique divisibility and checks relations by cancellation.

The inherited blueprint.from.node is null. The read-only blueprint_refs.py ancestor command confirms null for this item's created.item chain; it was retained and the new split_report explains the inherited BLR trait-extension input. Searched the whole imported blueprint for dilatation, blowup algebra, A[I/a], principal ideal, division algebra and localization of affine blowup. Read the current latest unit and direct-image proof under literature/blueprint/latest; its operation-preservation route is unchanged. No unit realization field is due: this item is not the unit's key theorem. No SGA source is used.

## Not duplicates

No new nodes. Reused def-nagata-blowup-chart-ring, lemma-nagata-chart-ring-normal-form and lemma-nagata-chart-ring-fraction-equality rather than creating a second blowup algebra. The generic blowup universal-property node does not supply the affine flat-test divisibility calculation by its stated conclusion, and is not cited. The calculation is short enough to be an elementary proof step using the two precise existing chart lemmas. Likewise generator independence, localization, group axioms and local finite generation are explicit proof steps, not clause-restating new nodes.

## Review by Q45

I read the item's full statement, its source designation, the existing DAG chapter and unit, the latest blueprint unit and direct-image proof, and delivery-errors B–E in both copies in the file. I read BLR §3.2 in the primary-source scan: Proposition 1 uses arbitrary flat test schemes, and Proposition 2(d) supplies the group construction motivation. I separately read Stacks algebra.tex at lemma-characterize-Dedekind (034X) and the affine blowup algebra definition and lemma-affine-blowup (052Q, 07Z3), more-algebra.tex at lemma-dedekind-torsion-free-flat (0AUW), and morphisms.tex at lemma-flat-characterize (01U5). The actual dependency statements, rather than extra claims from their proofs, are the interfaces used in this delivery.

Step 1 uses the localization-at-a-maximal-ideal DVR statement with the given Dedekind domain. It writes out how finite generation of the maximal ideal spreads its local generator to D_h, ensuring V(pi) is exactly the chosen closed point. The Noetherian definition, locally Noetherian affine-cover definition, local finite type permanence, and affine-open Noetherianity statements justify finite generation of each individual chart ideal. The chart algebra definition supplies exactly A[I/pi]. All seven cited statements were read. No global finite type assumption was substituted for local finite type.

Step 2 uses exactly the normal form x/pi^n with x in I^n and the equality criterion pi^k(pi^m x-pi^n y)=0. I checked the powers in the cancellation: after evaluation they yield pi^(k+m+n)(c-d)=0. This proves well-definedness, then the ring laws and uniqueness on generators. These are finite fraction calculations from the cited statements, not another theorem silently assumed. No claim of injectivity of A into C is needed.

Step 3 uses the affine flatness criterion for the actual chart U in G over Spec D; flatness as tensor-injectivity proves D-torsion-freeness without a separate flat-implies-torsionfree lemma. I checked localization preserves that property by the stated numerator calculation. The existing Dedekind torsionfree-flat statement allows arbitrary modules, so it applies to this subring even when it is not finite over D. The Spec flatness equivalence gives the chart scheme property. The finite-generator argument yields finite type over D_h and over D by adjoining 1/h; the special-fibre ideal equality is written out. These five statements were read and say just what the step takes from them.

Step 4 again uses the affine criterion on any flat test scheme, not just finite type ones. Because pi is a nonzero element of D, tensor-injectivity makes its action injective on each test chart. Scheme-theoretic factorization, not set-theoretic containment, gives phi(I) subset pi C. The affine-spectrum correspondence turns the ring lift into a morphism, and the scheme-morphism gluing statement supplies existence and uniqueness on the cover; restricting two lifts to affine subopens verifies agreement. All four cited statements were checked.

Step 5 uses the scheme etale source-target locality theorem for restricting a flat morphism to an open, with the separate open-immersion-is-etale node cited explicitly. Affine opens form a basis even if intersections are not affine; the proof covers intersections rather than treating them as affine. The flat-test property constructs inverse overlap maps and proves their cocycle. The scheme gluing statement gives exactly the charts and their intersections; the morphism gluing statement glues the maps and the universal property. Both gluing nodes allow arbitrary set-indexed covers. All five cited statements were read; the equality after inverting pi is proved by the two inclusions into A[1/pi].

Step 6 uses etale locality and open-immersion etaleness for flatness/local finite type, affine-local-target for affineness, affine permanence only for separatedness of d, and the two closed-immersion permanence statements for the displayed diagonal factorization. It does not cite affine permanence as though that node asserted composition of separated maps. Smooth-flat is used only to specialize the already proved flat-test property. These seven cited statements were read; no smoothness of G or G' is introduced.

Step 7 uses flat base change and transitivity to justify flatness of all finite powers, and the group-scheme definition for the original group diagrams and the meaning of the new ones. The subgroup hypothesis makes the fibre maps land scheme-theoretically in F. Uniqueness compares maps with the same composite into G, on each indicated flat source, proving associativity, units, both inverse identities and commutativity. This is a short formal assembly, marked elementary with those three cited interfaces. It does not assume that d is a monomorphism on arbitrary schemes.

Step 8 uses only the chart algebra definition; the unit-change and localization formulas are proved on their generators, and independence of charts follows from the flat-test uniqueness proved above. Localization uses the full multiplicative set D minus m, not an identification of D_s with a Zariski neighbourhood. The canonical group operations remain compatible because they were unique lifts. This also explains precisely why no quasi-compactness hypothesis is used.

I tested I=(pi), giving B=A and the identity dilatation; I=A on a chart disjoint from F, giving B=A[1/pi] and an empty special fibre; the additive group with identity centre, where D[x][(pi,x)/pi]=D[t] and x=pi t; nilpotent/zero-divisor elements of a flat chart algebra (only pi must act regularly, never every element of A); and the zero chart ring/empty test scheme. Nonflat test schemes are deliberately excluded from cancellation: for C=D/pi, multiplication by pi is zero and division need not be unique. Every group identity uses a flat finite power of G', where uniqueness does hold. Every step is below 2000 characters, and I reviewed each for a hidden lemma. There are no new statement-only nodes to test or source separately, and no cycle or unsupported citation was introduced.

## Verification and remaining work

Server check_dag returned OK, introducing no finding. Server review_split returned PASS with 0 new nodes. The required full deliver.py --no-push and push results are recorded by the delivery tool. No Lean file was written and no compiler, Lake or build command was run. The maintainer's independent review remains the next stage; there is no unfinished worker split.
