## Worker report

Files written:
- dag/nodes/sec-proper-base-change/prop-weil-proet-finite-proper-base-change.json: statement, split by degree-zero specialization of the existing bounded-below theorem; no Mathlib match.
- citations.json: verbatim statements for every citation in the three proof steps.
- searches.jsonl: actual msearch.py results, summarized with identical tool/query text in the item's mathlib_searches.

New nodes: none. Mathlib leaves: none. No unit file was changed: this is an endpoint specialization, while the unit's realized statement and three route steps already belong to thm-weil-pbc-bounded-below and lemma-weil-pbc-torsion-assembly.

Attachments: none. The search for this blueprint tag in WeilConjectures/ returned no declaration. The concept search found AlgebraicGeometry.Etale.isIso_baseChange_of_isProper (WeilConjectures/SixFunctors/Etale/BaseChangeTheorems/Proper.lean:121 in the source inspected), which states the more general theorem and calls hasTorsionBaseChange_of_isProper. The existing audit of its DAG node is rests_on_sorry, so it is not a finished attachment. No master sorry is treated as a proof.

WANTED: none.

What was wrong or changed: the imported proof_deps contained coherence and torsion-assembly ids not used by its detailed proof. I replaced it by the exact union of the actual step citations, wrote the elementary cohomology calculation out, and added def-weil-proper-morphism as a statement dependency for the existing word 'proper'. The statement itself is unchanged. Its title/id mention finite/proet, but its mathematical content is arbitrary torsion abelian sheaves on the etale site, not condensed E-modules or pro-etale modules; the proof makes no coefficient-category identification. The earlier sketch has naturality, identity and horizontal/vertical pasting clauses absent from the imported Detailed form. I have not added these clauses to the item's statement. They remain a provenance discrepancy for the second reader/maintainer; the split proves the detailed statement actually assigned.

Nothing remains unfinished in this one-level split. Its theorem dependency remains the existing bounded-below node with its own open proof obligations.

## Not duplicates

No new nodes. The whole-DAG and blueprint searches for torsion sheaves and exchange morphisms found lemma-weil-pbc-torsion-assembly, whose statement is equivalent to this item's detailed statement, so it is recorded in blueprint.same_as. thm-weil-pbc-bounded-below is a genuine generalization and is cited, not copied. Search for the 095T tag found both existing nodes and the projective-line/reduction nodes. No duplicate elementary single-complex lemma was introduced.

## Review by NB

I read the item's master blueprint file, both its first sketch and Detailed form, the chapter sec-proper-base-change record and unit sk-thm-properbasechange record. The unit route is projective line, proper reduction, then prime-factor devissage and the filtered union of torsion parts. Reading all seven proof steps of thm-weil-pbc-bounded-below confirmed that this route is already retained in its steps 1–3 before the derived spectral-sequence extension. Using that theorem at degree zero therefore preserves the unit route. The item is not the unit's key node and does not alter its realization record.

For the literature I read Stacks etale-cohomology.tex, Tag 095T (theorem-proper-base-change, statement and initial reduction to P1) and Tag 0DDE (lemma-proper-base-change, full statement and proof). 095T has precisely a proper f, arbitrary g, the cartesian fiber product, and an abelian torsion sheaf; neither finite presentation nor invertibility of the torsion orders occurs. 0DDE replaces the sheaf by a bounded-below complex with torsion cohomology and gives the same canonical map. Its spectral-sequence argument is implemented below the existing bounded-below node, not treated as an uncited elementary argument in this item. There are no new-node sources to review.

Step 1 uses the actual statement of def-weil-pbc-derived-categories: cohomology is kernel modulo image, D+ means vanishing below a bound, and torsion cohomology is the torsion condition for every cohomology sheaf. The actual statement of def-weil-pbc-etale-sheaves gives the local-section meaning of torsion. For the complex with only F in degree zero all differentials vanish, so its degree-zero kernel/image quotient is F and all others are zero. Every section of zero is killed by 1; no closure lemma, injective resolution, or sheaf-level torsion-characterization equivalence is being invoked. Thus the step is elementary with these definition citations. Bound 0 works even for F=0.

Step 2 uses exactly the statement of thm-weil-pbc-bounded-below: for a cartesian square, proper f, and every K in D+ with torsion cohomology, Ex at K is an isomorphism in D+(Y'_et). The same square and f meet the first two hypotheses directly, and Step 1 meets the two hypotheses on K. The theorem imposes no condition on g, schemes being Noetherian, a base field, constructibility, a fixed annihilator, or invertibility of torsion. I did not take any construction from the theorem's proof. This is the only non-elementary invocation and has its existing node citation.

Step 3 uses the statement of def-weil-pbc-derived-exchange, which defines Ex_square as a natural transformation of the same two D+ functors and defines Ex_square,K as its component, explicitly by the adjunction mate. It is not being cited for a termwise-resolution comparison. The symbol F in the item denotes F as a degree-zero object when derived direct image is applied. Substituting F[0] into that component is the same morphism, so no unproved transport between different exchange maps or different coefficient categories is needed. I corrected the text to say this definitional equality explicitly.

I checked the small cases F=0, an empty source scheme, an identity square, a sheaf killed by a single prime, and a torsion sheaf with no uniform annihilator. The single-complex calculation and the theorem's hypotheses cover all of them. No non-torsion sheaf is slipped in, and no bounded-above condition is used. The statement definitions of the cartesian square, proper morphism and etale sheaves were opened and agree with the source. The original sketch coherence clauses are reported above; no claim about those extra clauses is being inferred from a definition node.

Against delivery-errors B–E: there are no new statement-only nodes, hollow data, new Mathlib leaves, or self-containedness defects to conceal; TeX uses single backslashes in decoded JSON. Every proof citation has a complete verbatim statement in citations.json. The exact proof-dependency union excludes unused old ids. Steps 1 and 3 are written elementary computations, while Step 2 has its theorem node. Nothing was moved into a new lemma, and there is no new circular dependency; the existing bounded-below proof does not cite this item. Blueprint.same_as records the already-present equivalent torsion-assembly statement. Definitions from other units name the objects; the theorem argument stays in this unit, so no off-unit theorem tool is needed.

Mathlib searches were made only through msearch.py, including a second semantic phrasing and a second grep confined to AlgebraicGeometry/Sites. LeanFinder returned underived pushforward comparisons and etale stability, Loogle returned IsProper.isStableUnderBaseChange, and grep found no derived proper-base-change declaration (the site grep found stability of covering properties). I read PushforwardContinuous.lean's underived pushforward/pushforwardComp declarations and Proper.lean's base-change stability instance; neither asserts the item. LeanSearch returned Internal Server Error and is recorded unavailable, not as evidence of absence. No search was invented.

## Second reading by NB

- Item statement: checked against the detailed blueprint node and Stacks Tag 095T (`theorem-proper-base-change`), including cartesian square, proper `f`, arbitrary `g`, and torsion sheaf; verdict correct.
- Step 1: checked the degree-zero complex calculation against `def-weil-pbc-derived-categories` and the local-section torsion definition in `def-weil-pbc-etale-sheaves`; verdict elementary and valid, including `F=0`.
- Step 2: checked every hypothesis against `thm-weil-pbc-bounded-below`; cartesian square, properness, bounded-below complex, and torsion cohomology are all present; verdict citation supplies exactly the conclusion.
- Step 3: checked the exchange component and degree-zero interpretation against `def-weil-pbc-derived-exchange`; verdict the same derived functor component is used, with no termwise-resolution claim.
- New nodes: none; therefore no new-node statements, sources, Mathlib leaves, or searches require review.
- Edge cases checked: zero sheaf, empty source, identity square, prime-torsion sheaf, and torsion with no uniform annihilator; no hypothesis or conclusion changes were found.

Changes made in this second reading: none to the node or citations; the worker's proof-dependency cleanup and explicit `F[0]` identification remain correct. I verified the report, statement, proof citations, blueprint equivalence, and recorded Mathlib searches against the repository files and source text.
