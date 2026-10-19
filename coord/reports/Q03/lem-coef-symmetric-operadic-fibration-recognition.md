# Worker report: lem-coef-symmetric-operadic-fibration-recognition

## Files written

- dag/nodes/sec-six-functors/lem-coef-symmetric-operadic-fibration-recognition.json: item, statement unchanged, seven proof steps, status split.
- dag/nodes/sec-six-functors/lem-coef-pattern-induced-fibration-test.json: new statement-only input; no Mathlib match. This is the fully scaled general categorical-pattern theorem, not an operadic Segal assertion.
- dag/nodes/sec-six-functors/lem-coef-finite-relative-product-mapping-test.json: new statement-only input; no Mathlib match. This is a finite relative-cone mapping-space criterion, with no operads, markings, model structures or fibrancy in its statement.
- citations.json: verbatim statement quotes for every citation in every item step.
- searches.jsonl: actual msearch output records. The item's earlier searches are retained in its JSON. The two new nodes record only searches run in this session.

## Attachments

None. Searches under /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the exact item id, symmetric operads, operadic fibrations, and the two proposed generic results found no declaration giving these assertions. Ordinary derived-category Kunneth relative products are unrelated. No master sorry declaration is counted as a proof. No Lean source was changed and nothing was compiled.

## WANTED

WANTED: Jacob Lurie, Higher Algebra, 2017, Remark B.0.27 and Proposition B.2.7, for lem-coef-pattern-induced-fibration-test; Definitions 2.1.1.10 and 2.3.3.28 for the item. [Author PDF](https://people.math.harvard.edu/~lurie/papers/HA.pdf) read online, not archived under literature/.

WANTED: Jacob Lurie, Higher Topos Theory, Definition 4.3.1.1 and Remark 4.3.1.2 (dual relative-limit convention), for lem-coef-finite-relative-product-mapping-test. [Author PDF](https://people.math.harvard.edu/~lurie/papers/HTT.pdf) read online, not archived under literature/.

The worker brief prohibits downloading missing literature. No repository literature file was written. The item's proof_origin is therefore agent. There is no Stacks tag for either infinity-categorical result, and no SGA source is used.

## What needed repair

The imported item was statement-only. Its mathematical statement is retained, including arity zero, relative mapping-space fibers over edges of P, and the absence of active cocartesian lifting assumptions. No statement dispute was found.

The source citation to HA Proposition 2.1.4.6 alone would not be enough: its proof prints binary decomposition cones, whereas this item fixes all-color projection cones, including the empty cone. I do not equate their cone lists. Instead I verify the fibered-object definition directly for the exact pattern in the item, then use the general theorem B.2.7 with its explicitly induced pattern on P. This avoids importing an unproved comparison of two model presentations.

The source's Definition 2.3.3.28 is relative over an approximation. Using the general pattern theorem avoids having to prove that the identity is such an approximation and avoids any stronger active-lift assumptions. The item already assumes the categorical fibration needed there, although the fibered-pattern criterion suffices at the last step.

During self-review I repaired the passage from arbitrary cocartesian sections of a pullback to global cocartesian legs. The argument now compares each local lift with an existing global lift using the initiality lemma, identifies the comparison as an equivalence in the target fiber, applies the mapping criterion to that equivalence, and then uses cocartesian composition. This argument is written in steps 2 and 5; it is not hidden behind the words 'pullback section'.

## Not duplicates

lem-coef-pattern-induced-fibration-test vs lem-coef-categorical-pattern-model-calculus: the existing theorem supplies a model structure, its fibrant objects and its enriched model axiom. It does not characterize an arbitrary map to a fibered target by a pattern on that target. The new node states HA B.2.7(a) iff (c), with the induced pattern spelled out.

lem-coef-pattern-induced-fibration-test vs lem-coef-marked-operadic-model-structures: the existing node concerns ordinary/generalized NONSYMMETRIC operads over Delta-op and mapping objects. It does not give the induced-pattern criterion for arbitrary fully scaled patterns.

lem-coef-finite-relative-product-mapping-test vs def-coef-infinity-relative-cone: the definition tests the square of transformation spaces for all test cones. It does not state equivalence with the pointwise homotopy-fiber product test.

lem-coef-finite-relative-product-mapping-test vs lem-coef-infinity-join-cone-calculus: the existing node identifies cone categories and their mapping spaces. The new node is the relative universal-property criterion obtained from that calculation, including the pointwise homotopy-fiber test; it is not already a clause of that node.

lem-coef-finite-relative-product-mapping-test vs lem-coef-infinity-cocartesian-mapping-criterion: the existing node concerns one cocartesian edge with mapping spaces OUT of its source and target. Our finite relative LIMIT cone uses mapping spaces INTO its vertex and all its output vertices, allows the empty set, and does not assume those legs cartesian or cocartesian.

lem-coef-finite-relative-product-mapping-test vs lem-coef-relative-limit-initial-components: that node reduces an already existing relative limiting cone to initial objects of disconnected components. It supplies no mapping-space test even in the discrete case.

Whole-DAG keyword searches, exact B.2.7/source-place searches, source-declaration searches, and blueprint_refs searches for 'pattern', 'induced pattern', 'operadic fibration', 'relative limit', 'relative limit mapping', 'relative product mapping', 'discrete product', and 'fibration between' preceded creation. Broad relative-product hits were ordinary algebraic geometry, not this result. The nearest blueprint ancestor is prop-coef-integral-exceptional-adjoint; both nodes retain its exact inherited place and add this item at the front of via. No blueprint node states either result. There are no shared Stacks tags to distinguish.

## Argument behind the unsplit mapping-test input

This paragraph records the intended proof for its future worker; the new JSON has only a statement and no proof steps. For a finite discrete I, a cone is exactly a vertex x with one edge to each x_i. The mapping formula in lem-coef-infinity-join-cone-calculus expresses a transformation into this cone by a vertex map, its boundary maps, and the paths witnessing their commuting triangles. Apply this formula in D and B to the transformation-space square defining a relative limit. The square is a homotopy pullback exactly when, for each a, the pointwise square

Map_D(a,x) -> product_i Map_D(a,x_i)

Map_B(pa,px) -> product_i Map_B(pa,px_i)

is a homotopy pullback. In one direction choose the constant test cone on a; its transformation mapping space into q identifies with Map_D(a,x) by the same formula. In the other direction the pointwise square supplies the needed equivalence on the vertex maps, and adjoining the fixed boundary maps and their paths is a homotopy base change, so supplies the square for any test cone. Taking homotopy fibers over each vertex u of Map_B(pa,px) turns the pointwise pullback criterion into the displayed product of homotopy fibers, since the target map into a product has component maps and its homotopy fiber over a tuple is the product of their homotopy fibers. Conversely equivalence on every such homotopy fiber detects an equivalence over that mapping space. This last space-theoretic detection and the cone calculation are genuine content of the new unsplit input; the item does not pretend that they are elementary. This is a derived specialization of the dual HTT relative-limit definition, not a claim that HTT prints this formula verbatim.

## Review by Q03

I read coord/delivery-errors.md B-E in full, the worker brief and stage-1 rules, the chapter sec-six-functors and unit sk-prop-sf-biduality-general records, the inherited ancestor, and the current main-20261015 integral-exceptional-adjoint proof, especially its paragraph 2 finite derived mapping-complex comparison. This is a generic operadic foundation below the inherited coefficient-system route. I did not change a chapter, unit, target, maintainer-owned field, or the ancestor's statement.

For the item I read HA Definition 2.1.1.10 and Remark 2.1.1.14 (the precise fiber equivalence), Proposition 2.1.4.6 and its printed binary-pattern proof, Definition 2.3.3.28 and Proposition 2.3.3.30 (the relative context), Remark B.0.27 and Proposition B.2.7 including its (c)-to-(b) proof. For the first new node I checked that B.2.7 requires the base marking to contain all equivalences and that our full scaling meets its triangle assumption; these are retained in the general statement. For the second I read HTT Definition 4.3.1.1 and Remark 4.3.1.2 and the existing join-cone-calculus statement; its source explicitly identifies the pointwise formula as an agent-derived specialization, with its reasoning above. Neither new node has a proof or proof dependencies.

Step 1 uses the actual definition of categorical pattern (small cone list, all its edges marked) and the horn definition of inner fibration. The cone on the empty discrete set really is a vertex, not a missing condition. Filling a base horn and then lifting is the complete elementary argument that P is a quasicategory.

Step 2 uses the straightening statement's explicit values, transport and finite products in Cat-infinity; the product equivalence is a hypothesis of the item. The horn definition supplies base change of chosen globally cocartesian lifts. I checked the additional initiality statement supplies equivalence of the two lift targets IN THE FIBER, and the mapping criterion supplies global cocartesianness of the vertical equivalence; cocartesian composition is explicitly in the initiality/composition node. Thus every section being tested has the right inert legs. These are actual statement clauses, not facts borrowed from proofs of dependencies.

Step 3 applies exactly the new finite relative mapping criterion to p and to each particular inert cone. Its hypothesis is the item's operad mapping-product axiom over EACH pointed map, including degenerate maps. There is no assumption that mapping spaces over the underlying base category suffice for the later relative calculation.

Step 4 uses exactly the four defining pattern conditions already verified and the existing model-calculus clause 'its fibrant objects are exactly the P-fibered objects'. This is elementary substitution. It does not take the desired fibration conclusion from the model-calculus definition or enrichment.

Step 5 uses the new general theorem's explicit description of the induced cones, the categorical-pattern definition, straightening's actual fiber/transport identification, and the same local/global edge comparison justified in step 2. All induced cones are inert lifts of color cones, so the item assumes the relative fiber equivalence for EVERY such cone. No color fiber is silently assumed presentable. The categorical fibration gives an inner fibration between quasicategories as required; total E is checked by the same horn argument.

Step 6 applies the finite relative mapping criterion to r, with superscripts now edges of P. The item quantifies over every u, a, b and choice of cocartesian projections, so it gives exactly the test for every section; the local/global comparison in step 5 justifies the choice of projections. In arity zero it asserts contractibility of every relative mapping fiber, as required by a relative terminal cone.

Step 7 uses the general theorem's fibered-induced-pattern iff model-fibration statement after all its conditions have been proved, and the already verified target fiberedness. Its extra base-marking hypothesis holds because equivalences in the ordinary nerve of Fin_* are pointed bijections and every such bijection is inert. No nontrivial inference is assigned to an uncited definition. Active lifts do not enter any step. All dependency statements were opened, and citations.json copies their text verbatim.

For B1-B9 and C1-C8: new statements introduce all their objects and definitions, use single-escaped TeX, contain no proof sketch in the statement, and have complete source places. Actual msearch LeanFinder searches with two phrasings, Loogle, LeanSearch and source grep were run for both. Hits were ordinary category limits, generic fibration classes and Kan-Quillen horns; their types do not mention this structure. No exact or one-line Mathlib specialization was found, so both are unsplit and there are zero Mathlib leaves. No new node is a clause of the item: the nontrivial operadic verification remains in seven item steps, and both inputs are general structural tools. All proof citations stay in the same unit or cite definitions.

For D1-D5 and E1-E7: tested the new pattern theorem at the point pattern with no cones (recovering the categorical-fibration situation), the identity of any fibered object, and empty total spaces where fiberedness can hold. Its base equivalence-marking assumption was not dropped. Tested the mapping test for empty I (relative terminality), singleton I (the cartesian-edge mapping criterion), p=id (all homotopy fibers are points, so any cone is relatively limiting), and B=point (ordinary finite product mapping property). The item was checked at n=0 and n=1 and with empty unary color category; existence of a nullary vertex is retained by the n=0 fiber condition, so no false nonemptiness is deduced for unary colors. The two main corrections were avoiding the binary-pattern identification and explicitly justifying global cocartesian legs. No source statement was changed, and the statement checks found no dispute.

## Unfinished work

Only the permitted next-level obligations remain: the two new generic statements are unsplit. The item is fully split. The fresh second reader must review and deliver; this worker runs only the no-push dry run.

The first full dry run returned two textual checks. I removed an incidental use of the word for an uncompleted review from the signed review paragraph and replaced a possessive reference to the task with the explicit chosen-cocartesian-projection hypothesis in step 5. Neither change alters the mathematics.


## Second reading by Q03

The final split has one new statement-only node and zero Mathlib leaves. This section supersedes the first reader's counts and the proposal to retain the finite-relative-product mapping-test input; all earlier sections, including `## Review by Q03`, are preserved as the review history. I read delivery-errors B-E, dag-sync.md, GOAL.md, the item, all cited statements, and the definitions of relative cones and mapping composition. No repository or Lean source was written and no compiler, Lake, global build, or local delivery preflight was run.

- Item statement: checked against Higher Algebra Definitions 2.1.1.8 and 2.1.1.10, Remark 2.1.1.14, Definition 2.3.3.28 and Proposition B.2.7; PASS, unchanged. The mapping fiber over a pointed map agrees with the source's union of components because the nerve of Fin_* has discrete mapping spaces. The all-color cone list is checked directly, without asserting equality with the binary cone list of Proposition 2.1.4.6.
- Step 1: checked against the categorical-pattern and inner-fibration definitions and HA Definition 2.1.1.10; PASS, including the vertex cone for n=0 and degeneracies in the marking.
- Step 2: checked against the actual straightening statement (fibers, transport, finite products), the initiality/composition statement and the cocartesian mapping criterion; REPAIRED the inverse/precomposition justification by explicitly citing mapping composition and its inverse triangles, associativity and unit laws. The horn pullback argument uses its prescribed base simplex and no converse base-change assertion.
- Step 3: checked against the join-cone mapping-space formula, its naturality for boundary restriction, the definition of relative limit and the contractible-homotopy-fiber criterion; REPAIRED to the displayed two pullback reassociations using the operad output axiom. The fiber of the comparison is explicitly identified, so no uncited fiberwise-equivalence theorem is used.
- Step 4: checked against all four fibered-pattern conditions and the model-calculus clause identifying fibrant objects; PASS, elementary substitution after steps 1-3.
- Step 5: checked against the induced-pattern statement, the fiber equivalence assumed for every inert cone, straightening, initiality, mapping criterion and composition; REPAIRED to spell out both the prescribed-base horn filler and the comparison l=h g in E_{x_i}, replacing the reference to repeating step 2. The inverse/precomposition calculation now has its own citation.
- Step 6: checked against the relative output hypothesis for every edge u of P and the same existing join-cone and contractible-fiber statements; REPAIRED with the entire mapping-space pullback calculation written for E and P, including arbitrary test cones and the empty cone. No fibers over P are identified with fibers over Fin_*.
- Step 7: checked against HA B.2.7(a) iff (c) and the retained new node; PASS. Base equivalences are pointed bijections, hence inert, and all triangles are scaled; the target is already fibered. No active-lift hypothesis is introduced.
- New node lem-coef-pattern-induced-fibration-test: compared hypothesis by hypothesis with HA Remark B.0.27 (printed p.1469) and Proposition B.2.7(a),(c) (printed p.1488); PASS. The all-scaled convention supplies B.2.7's triangle condition, and the equivalence-marking assumption is explicit. It is a general theorem, not an operadic clause or an elementary consequence of the existing model-calculus statement.
- Former new node lem-coef-finite-relative-product-mapping-test: compared with HTT Definition 4.3.1.1/Remark 4.3.1.2 and the existing relative-cone definition and join-cone calculation; REMOVE as an elementary consequence in the direction the item needs. Its mathematical claim was not disputed, but a new obligation is unnecessary.

Small cases: the removed mapping test at empty I becomes relative terminality, at singleton I becomes the cartesian-edge mapping property, over a point becomes the product mapping property, and for p=id its comparison is an identity. In the repaired steps, empty products make H,V and their base counterparts points, yielding M equivalent to its base mapping space exactly as required. For the retained pattern theorem the point pattern with no cones recovers categorical fibrations with equivalence markings, the identity of a fibered object satisfies both sides, and the empty-object cases are governed by the explicit fibered-target assumption. For the item, n=1 is the unary projection, n=0 forces the nullary fiber to be terminal, and empty unary colors do not force a unary object to exist. No statement dispute was found.

Independent duplicate and attachment checks: searched DAG statements and the current blueprint for induced patterns, B.0.27/B.2.7 and relative-limit mapping tests; blueprint_refs returned zero matches for 'induced pattern' and 'relative limit mapping', and its ancestor command confirmed prop-coef-integral-exceptional-adjoint. Opened the nearby pattern-fibered-edge-detection node (it detects weak equivalences by edge pullbacks, not fibrations), the nonsymmetric operadic results, and relative-limit-initial-components; none states the retained theorem. Searched both read-only Lean source trees for the exact item id and categorical-pattern/preoperad/operadic-fibration vocabulary; no matching declaration was found. Ordinary RelativeLimitPresentation declarations concern pro-categories, not these quasicategorical assertions. A nonexistent Comparator directory in master was excluded from the successful repeated search; no source was counted as closed on the basis of a sorry declaration.

Independent Mathlib searches were run through msearch and remain verbatim in searches.jsonl: 'Marked simplicial sets fibrant over a categorical pattern: induced categorical pattern on a fibrant target' returned Kan-Quillen horn generators and generic fibrant-object predicates, with no categorical-pattern recognition theorem; 'The Yoneda embedding detects limits by homotopy pullbacks of representable mapping spaces, including relative limits' returned ordinary-category Yoneda/limit declarations, with no quasicategory homotopy-fiber statement. The retained node records the new pattern query and actual result. Its earlier searches were retained. No service error was reported as no match.

Changes and reasons:

1. Removed lem-coef-finite-relative-product-mapping-test and replaced both uses with explicit elementary calculations from already existing statements, avoiding an unnecessary unsplit node.
2. Replaced the step-5 repeat-of-step-2 shortcut with its full local/global edge comparison and horn filler argument, as E5 requires.
3. Added the mapping-composition citation and inverse argument in steps 2 and 5; added the contractible-fiber citation and explicit fiber computation in steps 3 and 6, satisfying C1-C4.
4. Updated proof_deps, split summary and proof origin to describe the final one-node split; regenerated citations.json with one exact statement quote for every final citation, and recorded the independent search for the retained new node.

The sole new node is self-contained, statement-only, uses single-escaped TeX, names its defining nodes, and has exact author-PDF theorem/remark references because Stacks contains no such infinity-categorical theorem. Both author PDFs were opened online for this reading; no missing literature was downloaded. No SGA source is used. The blueprint/unit route is unchanged. Required server dry run and delivery follow this completed report.
