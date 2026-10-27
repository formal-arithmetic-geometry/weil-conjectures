# Q103 — lem-sp-nested-affine-orientation

## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-nested-affine-orientation.json`: statement; split using existing nodes only; no Mathlib match for the full normalized chart comparison.
- `citations.json`: 21 step/node citations, each quoting a verbatim part of the cited statement.
- `searches.jsonl`: actual Mathlib searches made through the prescribed msearch command.

There are **0 new nodes and 0 Mathlib leaves**. `write_split.py` and `refine_split.py` are sandbox-only preparation scripts, not DAG files.

## Attachments

None. I searched the project `lean/WeilConjectures/` for the exact blueprint id, nested affine/orientation terminology, and the orientation/integration/purity notions in SixFunctors. The existing derived orientation interface and its package do not state both of this item's actual normalized morphism equations. No declaration qualifying for ATTACH was found. No Lean was written or compiled.

## WANTED

None. This is an agent-written assembly of existing DAG statements on the blueprint route, not a claim that a human source contains this exact expanded argument.

## Corrections and source comparison

The item's statement, its statement dependencies, its existing search evidence, its original source record and blueprint ancestry are retained. There is no statement dispute. Its proof was empty. The latest blueprint `sk-prop-sp-composition/sk-prop-sp-composition-factors.proof.md`, proof (1), is the source of the route: identify both nested chart orientations with ordered integration, then regroup the affine coordinate blocks. I read the current unit and chapter records, GOAL.md, the three-level policy in SETUP.md and delivery-errors B–E in full. The latest blueprint is the `main-20261024` snapshot recorded in COMMITS.txt; no old snapshot was used as source text.

The blueprint's short prose does not by itself provide the actual compatibility of the tensor comparison with the nested chart. I supplied the explicit substitution in the already existing `lem-pur-etale-cartesian-tower-tensor-comparison`; creating a new lemma for that substitution would duplicate the existing result. In particular, the square with horizontal maps bu and v is generally NOT Cartesian. The proof uses the Cartesian square of the affine projection under v, then the extra etale source map u, exactly as that lemma says.

The latest blueprint proof of projection-purity agreement still mentions higher composition coherence. This split uses the already repaired DAG statement of `lem-pur-projection-purity-agreement`, not that imported proof argument. I checked the dependency closure of every principal comparison used here: none reaches this item, so this reuse introduces no cycle.

## Unfinished work

None at stage 1. Existing dependencies retain their existing stage states. No new unsplit obligation is introduced.

## Blueprint and duplicate searches

I ran `tools/blueprint_refs.py ancestor lem-sp-nested-affine-orientation` (nearest ancestor: det-sp-composition-factors) and whole-blueprint searches for `orientation`, `nested affine`, `tensor base change`, `ordered affine`, and `chart`. I also searched all DAG statements/titles for ordered integration, chart restriction, tensor base change and composition. The existing chart, tensor-tower and ordered-regrouping lemmas cover the needed tools. `same_as` remains empty: the imported affine composition law and chart orientation lemma each cover one ingredient, not the full fixed nested-chart statement. Since no node is created, there are no new/existing same-tag pairs requiring a Not duplicates section.

## Mathlib search review

The sandbox log contains two semantic phrasings, two Loogle attempts, an algebraic-geometry source grep and LeanSearch. I read all returned hits. The first Loogle pattern reported unknown `CategoryTheory.NatIso`; I corrected it to `CategoryTheory.Adjunction.comp`, which returns composition, its Hom equivalence, counit/unit formulas and mate unitors. I read Adjunction/Basic.lean at lines 567–590: those facts give general adjunction calculus but neither diagonal normalization nor either geometric chart equation. The second LeanFinder query returned `AlgebraicGeometry.AffineSpace.isPullback_map`; I read AffineSpace.lean at line 325, which states the genuine Cartesian affine-space square, not a purity comparison. Other returned hits concern scheme normalization, manifold charts, or formally etale/smooth algebras. The Mathlib grep for `purity|dualizing|exceptional` in AlgebraicGeometry returned zero hits. Thus this item is not a one-line specialization of a returned declaration. No unrun query was recorded and no service outage was treated as absence.

## Review by Q103

I read the latest factors proof (1), the orientation-charts proof, projection-agreement proof, affine-composition proof, composition-coherence proof and purity-base-change-factors proof. I then opened the JSON statement of every cited node. The argument follows the unit's nested-chart/ordered-integration route; it uses no SGA source. No new lemma needs an independent source or Stacks tag because no new node is created.

For step 1 I checked the actual affine-space definition: adjoining the d coordinates gives the Cartesian square under v, and rank zero is the base. The etale base-change node states precisely that a base change of an etale map is etale (Stacks Tag 02GO); the composition/cancellation node states the needed composition clause. The noetherian, quasi-compact-open and finite-type-open statements give the hypotheses for all restrictions. A field is Noetherian by its two ideals, and finite generation is transitive; polynomial coordinate rings give the remaining elementary finite-type checks. The preservation theorem explicitly carries D^b_ctf to D^b_ctf, and the chart-domain lemma explicitly preserves it under inverse image, twists and shifts. I applied them with E=Q_l, level r, so the ring is exactly Z/l^r, and in particular G_{p_e}R is in the required domain, without assuming it flat or concentrated in degree zero.

For step 2 I checked that projection-agreement is an equality of the specified smooth purity map with the ordered integration transpose for every constructible finite-Tor input, and includes rank zero. The smooth-purity definition really factors through the inverse diagonal orientation and the counit-defined tensor map. The unit-composite lemma states that the tensor map at the coefficient unit is its unit constraint. These statements therefore give both a_P=Gamma_{P,R} and Gamma_{P,H}=t_{P,H}(1 tensor a_P), including H=G_{p_e}R. This is a substitution, not a fresh normalization assumption.

For step 3 I checked that the chart-orientation statement compares the DIAGONAL orientation with the inverse of the ordered integration transpose under the counit-preserving etale composition comparison. Inverting gives exactly the three inverse-orientation equations written in the proof. The base-change-factors statement explicitly says e_1 u^*a=a' in clause (1); I use it only for target-open restrictions and for the affine projection q under v. The chart-mate lemma supplies open and composable-etale compatibility, and the sigma-locality statement explicitly permits source-open restriction without a Cartesian source-open square. Composition-comparisons specifies the unique conjugate preserving the composite counit, which is the compositor fixed in the item's statement. This proves the first arrow formula with the specified comparisons, not merely an isomorphism of its endpoints.

For step 4 I checked every object in the Cartesian-tower lemma: its base B is S, its T is A^e_S, its A is A^d_{A^e_S}, its Q is V, its fiber-product R is A^d_V, G=v, H=u, J=b and F=bu. Its pair (a,b) is the restricted pair (f,g). Both vertical morphisms are smooth of the required dimensions; all extra horizontal arrows are the separated etale finite-presentation maps established in step 1. The final equation in the cited statement is exactly the comparison of sigma for this pair with the pullback of sigma_{p_d,p_e}. The proof explicitly substitutes the equations from step 3 into its two factors, cancelling beta^{-1} beta in the first and using the chart comparison of g in the second. Thus no orientation-composition assertion is smuggled into the transport.

For step 5 I checked the domains of both instances from step 2 and wrote the elementary tensor factorization of q^*a_p tensor a_q. This is the required second arrow formula, not an application of a node merely restating that formula.

For step 6 I checked that the imported affine composition law assumes d,e >= 1, so I do not use it for an empty block. For positive blocks it states exactly the displayed ordered composite and the positive even-degree interchange sign. For a zero block I use the ordered-regrouping lemma's explicit identity adjunction and repeated-endpoint cases with the exact recurrence of the affine comparison definition. The proof writes both d=0 and e=0 equations; when both vanish the affine maps are identities. This does not assert that an arbitrary dimension-zero etale chart map is an identity: those chart maps retain their normalized etale comparisons. For an empty scheme all the compared arrows are the unique zero-category maps. The arithmetic sign (-1)^((2d)(2e)) is 1 also when one block vanishes. Step 7 is substitution of the established equalities and functorial pullback only.

I checked B–E against this final file: no new statement-only node hides a proof, no new node is elementary/a duplicate/a clause restatement, every non-elementary use has a statement citation, and every citation quote occurs verbatim in its statement. The existing-item statement is unchanged. All seven proof steps are under 2000 characters (the maximum is 1347), and each is one explicit application or assembly rather than a concealed new lemma. The source and target of the equations, coefficient categories, orientation direction and the order of the two coordinate blocks were checked. The generic preservation, open-domain and affine-projection base-change tools are declared in split_report.tool_uses where appropriate; none replaces the composition unit's integration route.

An initial server `review_split` check passed before the report was written; its route note identified the preservation tool, now explicitly declared as well. Final delivery uses the required full dry run after this report.
