## Worker report

Item: `lem-sp-power-torsion-sheaf-limit-complete`, group Q101, stage 1, 2026-10-21.

Files written: `dag/nodes/sec-smooth-purity/lem-sp-power-torsion-sheaf-limit-complete.json` and the citation audit `citations.json`. The item is split into nine proof steps. Its statement, statement dependencies, origin metadata and existing Mathlib searches are retained; the proof, proof dependencies, proof origin, split report and additional actual search results are filled. No Lean was written or compiled. All writes were in this item's sandbox.

## New nodes

None: 0 new nodes, 0 new Mathlib leaves. The principal torsion argument and the two finite-coordinate comparisons are proved in the item's steps, rather than relabelled as new nodes carrying its clauses.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the exact blueprint tag and for Roos, power-torsion and derived-completeness terminology. Read the completeness interfaces in `CategoryTheory/DerivedCategory/Complete/Defs.lean`, `Principal.lean` and `NormalizedTowerLimit.lean`. In particular `DerivedCategory.derivedComplete_of_iso_isNormalizedAdicTower` and `DerivedCategory.IsNormalizedTower.derivedComplete` concern normalized towers and constant-ring module sheaves. They do not supply the item's arbitrary strict towers over the completed ring sheaf, its signed double-Roos comparison or its specified unit. They are not attachments. No Mathlib declaration is being offered as a project attachment.

## Sources and route

Read `GOAL.md`, the three-level rule in `SETUP.md`, the stage-1 brief and stage document, `roles/worker.md`, the chapter record `sec-smooth-purity`, unit `sk-lem-sp-tower`, and the current main-20261015 proof of that unit. This item realizes its sentence that the limit is derived complete because its levels are killed by powers of ell. It does not replace the unit's normalized finite-reduction calculation or its later constructibility argument.

Read Bhatt–Scholze, *The pro-étale topology for schemes*, Definition 3.5.2, Lemmas 3.5.4–3.5.7, Lemma 3.4.12 and its proof, Propositions 3.1.9, 3.2.3(1), and 4.2.8. Lemma 3.5.7's proof explains completeness of the limit; Lemma 3.4.12 supplies the principal two-term completion picture and its transitions. These paragraphs motivate the proof but are not used as an uncited substitute for DAG dependencies. The expanded proof is marked `proof_origin.by = agent`: it adds explicit strict models and the unit calculation rather than attributing those formulas verbatim to the paper.

Also read Stacks `sites-cohomology.tex`, Tag 0941 (`lemma-derived-limit-is-ok`), including its injective tower/product calculation, and Tags 06YT (`lemma-derived-tor-quasi-isomorphism-other-side`) and 06YY (`lemma-derived-base-change`). Read the cone definition in `derived.tex`, Tag 014E (`definition-cone`). The tensor convention cited in the existing tensor node is Tag 012Z (`definition-associated-simple-complex`) of `homology.tex`. No SGA source is used.

## Searches and reuse

Searched the entire DAG by title and statement for Roos, double Roos, iterated Roos, Koszul, nilpotent, power-torsion, countable-product exactness, and K-flat quotient comparisons. Ran `tools/blueprint_refs.py ancestor` for the item and whole-blueprint searches for `derived complete`, `Koszul` and `Roos`. No other blueprint node states the item. The item's existing `blueprint.from` correctly points to `sk-lem-sp-tower`, its precise completeness sentence, with empty via; `same_as` is empty.

Opened the statements of every cited node. Nearby nodes also inspected include `lem-sp-koszul-roos-projection-comparison`, `lem-weil-pbc-finite-free-strict-tower-transport`, `lem-pe-roos-cone-calculus`, `lem-pe-endomorphism-fibre-double-cone`, `lem-pur-regular-quotient-completion-unit`, and `lem-pur-roos-intrinsic-completeness-equivalence`. The finite-free ring-extension theorem is not used for tensoring with a two-term complex. The nilpotent completion nodes `lem-weil-pbc-nilpotent-koszul-graded-tower` and `lem-weil-pbc-nilpotent-koszul-completion-unit` concern constant coefficient rings; the present proof works directly with the actual sheaf R. No duplicate node was created.

Ran the required `msearch.py Q101 lem-sp-power-torsion-sheaf-limit-complete` searches: two LeanFinder phrasings, Loogle `"AdicCompletion"`, grep `derivedComplete|derived.complete|Koszul|Roos` in `Algebra/Homology`, and LeanSearch for derived completion and commuting homotopy inverse limits. Read all returned hits. Ordinary adic completion, local cohomology, limits of complexes, and localization lemmas do not state this theorem, and none is a one-line specialization to it. The actual queries and result summaries were appended to the item and are in `searches.jsonl`. Searches already present on the repository item were retained as provenance of its creation, not represented as new Q101 calls. All services used here answered successfully.

## Tool uses

The item's `split_report.tool_uses` declares its general-purpose ringed-site, tower and K-flat foundations. They provide exact countable products, the strict Roos comparison with its augmentation, levelwise abelian tower exactness, the short-exact-sequence triangle, the exact total derived limit and pro-zero criterion, K-flat resolutions and tensor/cone tests, and scalar extension. No statement in the reconstruction unit gives these general foundations. The proof does not use another unit to replace a mathematical step of normalized reconstruction. Maintainer-owned `tool_uses` was not written.

## Problems and unfinished work

No change to the item's statement was needed. The imported item had no proof; in particular the specified canonical maps and double-Roos sign had to be justified rather than inferred from an abstract existence of an isomorphism. The new proof does not assume a common torsion exponent or identify a normalized tower with an arbitrary power-torsion one.

No WANTED source, statement dispute or abandoned clause. Stage 1 proves the mathematical argument and cites its existing dependencies; it makes no claim that those still-open dependencies have finished Lean proofs.

## Review by Q101

I read delivery-errors B–E in full with the item, the dependency statements and the sources open. The item agrees with the completeness sentence of the current blueprint: arbitrary power-torsion levels suffice, and normalization is needed elsewhere in the unit, not here. I kept all clauses, including naturality, the sign in the double product, the actual quotient unit and the final triangle. There are no new statement-only nodes whose hypotheses or source tags need separate certification.

Step 1 uses exactly the assertion of `lem-weil-proetale-countable-products-exact` for a sheaf of commutative rings R on the pro-etale site of any scheme T. It does not assert exact arbitrary products. I checked `lem-weil-strict-roos-comparison` says both that the raw termwise Roos complex computes the total limit and that its zero shifted-coordinate augmentation is the specified derived map. This avoids silently selecting a lift in a triangulated category.

Step 2 uses the differential written in `def-pc-tensor-complex-sheaves`; I checked the off-diagonal term is `(-1)^(k+1) pi^j` and the quotient identification `y ↦ (-1)^k y` has differential `-d_Q`. The short exact sequence is a sequence of complexes of strict towers, not merely a collection of triangles in D(R). `lem-weil-tower-category-levelwise-abelian` explicitly makes that an abelian category with levelwise exactness, and `lem-weil-pbc-complex-ses-triangle` is stated for any abelian category, so it applies there. This step does not claim the quotient sequence is split as complexes.

In step 3 the composite transition on the quotient tower is pi^r_n even when j is less than r_n, and it vanishes termwise by the precise hypothesis on Q_n. The pro-zero statement of `lem-weil-pbc-ringed-strict-tower-homotopy-limit` and its exactness therefore apply. The identification of the constant-tower limit uses the displayed finite-sum section of `1-s`; it is a chain section because every coefficient is an integer scalar and the differential commutes with it. The augmentation normalization is exactly the last paragraph of `lem-weil-strict-roos-comparison`. This proves each u_Q_n and its naturality without choosing torsion exponents compatibly with n.

Steps 4 and 5 are finite coordinate calculations, kept as steps under B/D rather than made into nodes for clauses of the item. For step 4 I checked the four Roos bidegrees (0,0), (1,0), (0,1), (1,1): only the last is negated, and the n- and j-differentials acquire precisely the signs needed after interchange. The internal differential commutes with the comparison. The inverse has the same sign, and the inclusion lies in j-degree zero. For step 5 I checked both differentials on each (p,a,b) summand; L_j has only two rank-one terms, so no interchange with an infinite direct-sum totalization is asserted. The comparison commutes with `(pi,1)` and with projections, not only with differentials.

Step 6 uses the derived functor statement in `lem-weil-strict-roos-comparison` and the exact-evaluation statement in `lem-weil-tower-category-levelwise-abelian` to pass the levelwise quasi-isomorphism through Rlim_n. I checked the resulting map has j-degree zero and Koszul degree zero, hence its interchange sign is 1 and its shifted j-coordinate is zero. This identifies the completion unit itself, which would not follow from an unspecified isomorphism between the objects.

Step 7 takes regularity, the actual finite quotient identification, and the finite-free K-flat L_j resolution from the statement of `lem-sp-ell-coefficient-fiber`, not its absent proof. Its hypotheses are exactly the prime, finite extension, uniformizer and scheme already in the item; ell need not be invertible on T. `lem-pc-kflat-resolution` permits unbounded H_0. `lem-pur-kflat-tensor-quasiiso-independent` applies to f with K-flat second factor L_j. For the other leg I checked the cone criterion, the tensor/cone identification, and the K-flat acyclic-tensor definition. When the K-flat factor is written on the other side, the usual signed tensor interchange `x tensor y ↦ (-1)^(deg x deg y) y tensor x` identifies the two total complexes; this follows directly from the cited tensor convention. Scalar extension is computed on P by `lem-pur-derived-change-of-rings`, and restriction leaves the underlying abelian-sheaf complex unchanged by `def-pc-sheaf-restrict-scalars`. No K-flatness of H_0, B_j or Q_n is assumed.

Step 8 uses one P at all levels, so the quotient augmentation gives a strict tower map. The augmentation and transition statements used are in `def-pur-principal-koszul-quotient-towers`; its left-tensor formulas agree with the right-tensor version because the inserted unit has degree zero. I checked the literal square of the two inclusions and the tensor augmentation. This is why the quotient unit, not just an objectwise scalar identification, is preserved. The strict Roos comparison then passes the entire square to the derived limit.

Step 9 uses the natural Roos triangle in `lem-weil-pbc-ringed-strict-tower-homotopy-limit`. The final paragraph of `def-weil-derived-complete` explicitly allows transport of that triangle along an isomorphism with the specified first-map components. Thus the conclusion is exactly its definition of completeness, while our earlier steps prove the stronger specified-unit assertion requested in the item.

For E-type edge checks I tested zero complexes and the empty scheme, r_n=1, a zero transition n-tower, a constant pi-torsion tower, and the quotient tower Q_n=R/pi^n with exponents increasing without bound. In the last example no uniform exponent is used: each quotient j-tower is killed after its own n-step transition. Arbitrary negative and positive cochain degrees cause no infinite diagonal sums: there are two Koszul degrees and four double-Roos degrees. In characteristic 2 the sign formulas reduce to the same chain identities. Constant towers use the explicit chain section rather than an assumed vanishing of higher limits. These checks required no change to the statement.

Every cited node has a verbatim statement quote in `citations.json`. All proof steps are below 2000 characters. No source error was found. The correction during self-review was to avoid any appeal to a finite-free *ring extension* lemma for a finite-free *complex*: the two-term tensor/Roos comparison is instead proved directly in step 5.
