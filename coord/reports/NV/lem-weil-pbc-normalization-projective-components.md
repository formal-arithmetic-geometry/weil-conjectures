## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-normalization-projective-components.json`: statement item, split in ten steps; no full Mathlib match.
- `citations.json`: one verbatim statement quote for each of the 41 step citations.
- `report.md`: this report. `refine.py` and `searches.jsonl` are sandbox working records.

No new nodes and no new Mathlib leaves. The existing mathematical statement, blueprint ancestry, original searches, source references and maintainer metadata were retained. The existing nine-step argument was reused and audited; it was not replaced by a new lemma asserting the item's conclusion.

## Attachments

None for the full item. Searching the exact item tag, normalization_projective_components, and normalization/projectivity notions in the permitted slopmaster2 project source found only the curve-compactification discussion, which does not state this result for arbitrary projective schemes. Master was searched read-only and was not evidence of a finished proof. No Lean was written or compiled.

The already attached `lem-sc-normalization-exists` is used as a tool. Its recorded slopmaster2 declarations in `WeilConjectures/Mathlib/AlgebraicGeometry/Normalization.lean` were read: surjectivity at 197--202, finite normalization at 465--478, and dimension equality at 519--529. Their hypotheses are integral schemes locally of finite type over a field; the components in this proof satisfy them.

## WANTED

None. All sources used are present in the repository.

## Findings and corrections

The current shared node was unsplit but retained a previously reviewed proof and reports. I reused that proof and its citation route. The earlier report is `coord/reports/NY/lem-weil-pbc-normalization-projective-components.md`; its mathematical findings remain applicable. The corrected affine-base clause of `lem-fin-finite-over-projective` is essential: it is applied only to Spec k, never as a claim of a global projective-space embedding over an arbitrary Noetherian base.

I separated the old long step 4 into the affine normality calculation and the elementary generic-point calculation. The first now cites `def-pc-reduced-scheme` explicitly for reducedness from domain stalks. The second spells out both uniqueness of the point over eta and why its closure is the whole normalization. The only ring calculation is b=a/s and a=sb; the generic-point and fraction-field facts are already cited statements. No independent unstated lemma is hidden in either step. All steps are below 2000 characters. The finite-coproduct argument now states its induction and its binary induction step, with the empty base already explicit. Steps 1 and 2 cite the actual proper and finite-type definitions instead of relying only on their convention collector. The statement is unchanged; no STATEMENT-DISPUTED finding applies to this item.

The existing natural-language proof of `lem-sc-normalization-exists` still has the previously reported defects: it treats only dimensions zero and one although its statement is general, and infers lattice stability from coefficients that lie in the fraction field rather than the ground ring. It also says affine and dominant implies surjective, which is false (Spec k(t) -> Spec k[t] is a counterexample); integrality is needed. These defects are in a read-only dependency's imported proof, not its correct statement. The current audit marks that dependency closed, with the actual project declarations above. This item uses its statement, not any step of the defective imported proof.

## Unfinished work

None in this one-level split. The other nodes remain owned by their respective workers/maintainer. No chapter, unit, definition, target, live project or launcher file was changed.

## Not duplicates

No new nodes. Whole-DAG and blueprint searches for normalization, normalization projective, normal integral normalization, and finite over projective identified the existing tools. `lem-sc-normalization-properties` and `lem-sc-normalization-exists` concern integral schemes; neither states the arbitrary-projective-scheme component decomposition of this item. The normal integral-closure, localization, affine function-field, affine stalk and coproduct facts already have nodes, which are reused.

Mathlib was searched with msearch.py using both the full statement and the second phrasing “Finite normalization preserves projectivity and dimension of an algebraic scheme”, plus Loogle and source grep. The actual hits and queries were read and appended to the item's existing search records. In this session LeanSearch worked and returned relative-normalization declarations. The relative normalization definition/open charts and the integral-source instance in Mathlib/AlgebraicGeometry/Normalization.lean (especially lines 125--135 and 358--365) were read. Relative-normalization integrality alone supplies only part of the present item; it does not give finite absolute normalization, projectivity, the finite component decomposition, normal stalks and the other clauses. There is no full-item Mathlib leaf. Older unavailable-service entries were preserved as unavailable.

## Review by NV

I read the worker contract, delivery-errors B--E, the three blueprint levels, GOAL and dag-sync, and the item's chapter/unit. I read the current main-20261015 finiteness theorem and proof and followed its Stacks constructibility input through the recorded 0GK5 completion route. The split stays below that route: it supplies normalization of a projective completion, without replacing any proper-base-change or constructibility argument. The main blueprint's historical SGA reference is not used by this delivery. The proof uses only Stacks and the existing DAG tools.

For the item I read varieties.tex Tags 0BXR (`lemma-normalization-locally-algebraic`), 0GK4 (`lemma-normalize-projective`) and 0GK5 (`lemma-dim-1-projective-completion-after-insep`), and morphisms.tex Tags 035Q (`lemma-normalization-normal`) and 035O (`lemma-normalization-reduced`). These allow an arbitrary field and nonreduced projective C; the dimension restriction is conditional. No perfection, algebraic-closedness, connectedness or pure-dimension hypothesis was added. No new node requires an additional source audit.

Step 1: I opened the statements of projective-proper, proper and finite-type morphisms, quasi-compact schemes, locally Noetherian schemes, locally-finite-type preservation of local Noetherianity, and finite components of a closed subset of a Noetherian scheme. Properness supplies finite type, and its quasi-compactness applied to the whole affine base gives quasi-compact C. A field has just two ideals, hence Spec k is Noetherian; the preservation lemma applies. The finite-components node is applied with E=C and explicitly supplies the covering as well as finiteness. This is the initial argument of 0BXR; Properties 0BA8 was also read.

Step 2: I checked reduced-induced closed subschemes against Schemes 01J3/01J4 and read their uniqueness and affine description. The irreducible-component definition ensures each component is nonempty and irreducible, and the integral-scheme definition explicitly gives integral = nonempty, reduced and irreducible. Closed-immersion-finite states exactly the finiteness of the component inclusion (Morphisms 035C was read). In finite-over-projective, all three hypotheses hold: Spec k is Noetherian, C is projective in the global embedding convention, and the inclusion is finite. Its affine-base conclusion gives component projectivity. Projective-proper and the proper/finite-type definitions then supply finite type over k.

Step 3: I read both the definition and the full statement of integral normalization, not merely a tag or its proof. Integral finite-type Z_i over k meets every hypothesis of normalization-exists, which states finite, surjective and equal dimension. Nonempty Z_i and surjectivity imply nonempty N_i. The composite to C is finite by the exact finite-composition statement (Morphisms 01WK was read).

Step 4: I checked scheme sobriety and affine function-field statements: they supply the unique eta, the domain A and its fraction field K. The affine description is explicitly in def-fin-normalization-extension and agrees with def-sc-normalization at L=K; the current main blueprint definition was read. Integral-closure-normal applies to the finite extension K/K of degree one. Its actual statement supplies a normal domain with fraction field K. The affine-stalk node states localization at each prime (Schemes 01HV(6) was read), and normal-localization supplies an integrally closed domain there (Algebra 034L and 00GY were read). Cofinality of neighborhoods inside an open chart gives the same stalk in N_i directly. Domain stalks have no nonzero nilpotents, so the cited reduced-scheme definition applies.

Step 5: I checked the zero-prime generic-point clause of the affine-stalk/function-field node and the clause of the affine-function-field node that eta lies in every nonempty affine open. A prime over zero containing nonzero b would contain a=sb from A, a contradiction. Thus all charts share exactly one point over eta. Every chart lies in the closure of that point, so N_i is irreducible by the written closed-union argument. The cited integral-scheme equivalence now applies with reducedness from step 4 and nonemptiness from step 3. This is elementary after the explicitly cited chart facts, and is not a new normalization theorem in disguise.

Step 6: I checked the family-coproduct statement for open coprojections, disjointness, covering, closedness by the complement, and its mapping property. The finite binary-coproduct statement is precisely the induction step (Morphisms 0CYI was read). The empty scheme is Spec 0, whose coordinate ring is the zero finite module; this verifies the zero-summand case using the finite-morphism definition. Component covering and the component surjections prove surjectivity point by point.

Step 7: I reread finite-over-projective separately for the finite maps N -> C and N_i -> C. The source of these maps need not already be projective; it is exactly the conclusion of that lemma when the projective target lies over affine Noetherian Spec k. Projective-proper then supplies properness for every asserted structure map, as in 0GK4.

Step 8: I checked the identity-on-spaces clause of scheme reduction, the reduced-source factorization statement (Schemes 0356 was read), reduced-induced uniqueness and affine description (01J3), and the coproduct mapping property. On each affine of C the radical component ideal J_i contains the nilradical. The quotient R/J_i is unchanged when the ambient ring is replaced by its reduction. Thus these are the same component schemes with the same maps, not only homeomorphic spaces. The copairing gives the factorization, and the componentwise definition identifies it as normalization of C_red. No uniqueness of arbitrary image factorizations is assumed.

Step 9: I checked that the dimension definition uses chains of irreducible closed subsets with their strict inclusions. A closed component carries the same chains as closed subsets of C, so its dimension cannot be larger. Normalization-exists states the required equality with dim N_i. This handles dimension zero as well as one and does not impose any bound when the conditional hypothesis is absent.

Step 10: I checked the nonemptiness convention for irreducible components. If there are no components their covering makes C empty; an empty C has no such nonempty subsets. The empty coproduct and all individual-component assertions then have exactly the vacuous meanings stated.

I tested empty C, Spec k, the nonreduced zero-dimensional scheme Spec(k[e]/(e^2)), and a union of two intersecting projective lines. The last has disjoint components only after normalization, as used here. Over an imperfect field the normality proof is unchanged and claims no smoothness. The finite-family base includes I empty, and the conditional dimension statement does not force the existence of a one-dimensional component.

I checked B1--B10, C1--C8, D1--D5 and E1--E7 against the node and the actual statements cited. In particular, no definition is substituted for a theorem, no proof of another node is used as an interface, and no new clause-node or duplicate was created. The off-unit generic-tool declarations already present in split_report were retained; maintainer-owned tool_uses was not changed. Every step use has its verbatim statement in citations.json, proof_deps is exactly their union, and the mathematical statement is unchanged.
