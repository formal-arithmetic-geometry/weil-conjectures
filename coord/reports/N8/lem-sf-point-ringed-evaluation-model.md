# Stage-1 delivery: lem-sf-point-ringed-evaluation-model

Group N8; 2026-10-21. Direct delivery under the dispatcher's brief.

## Files written

- `dag/nodes/sec-six-functors/lem-sf-point-ringed-evaluation-model.json`: existing statement, now split into nine steps; statement unchanged; no exact Mathlib match.
- `citations.json`: 24 verbatim statement quotations, one for each step/node citation. Complete statements are quoted so that the representative, coefficient and constraint clauses used remain visible.
- `report.md`: this report. No new DAG nodes and no new Mathlib leaves.

The sandbox initially had only dispatcher marker files. There was no earlier item, report or search log to recover. The repository was read only; all writes, including the PDF extraction and working script, are under this item's sandbox. No git commands, Lean writes, compilers, Lake or local project-check scripts were run. The required delivery tool is used for the server commit and checks.

## Attachments

None. Searches of `lean/WeilConjectures/` by the item id and by point/evaluation/ringed/tensor concepts found no declaration stating every clause. `ProEtale.fieldGlobalSections` in `WeilSheaf/FieldCoefficientCohomology.lean` defines evaluation for a special coefficient model; it does not prove this arbitrary-ring-sheaf signed/derived/scalar assertion. The SectionsMonoidal file concerns evaluation on presheaves, so it is not an attachment for the sheaf and derived statement.

## WANTED

None for this split. The arithmetic results already have DAG nodes, including the Mathlib leaf for completeness; this delivery does not reopen their proofs.

## Findings and changes

The item was an unsplit node extracted from the ambient part of the parent point-fibre theorem. Its statement is true as written. I retained it, all statement dependencies and its exact blueprint ancestry. The unit and chapter route is unchanged: this is the point coefficient interpretation needed by the final compact-support specialization of relative Kunneth, not a new proof of that theorem.

The split explicitly distinguishes the topos-point inverse image, its module pullback with the identity ring map, and localization of exact sections. It uses existing generic results for normalized cochain tensor/coefficient equations and exact pullback with its resolving comparison; it does not infer such theorems merely from definitions. Scalar extension is computed on resolving models and is not asserted exact for arbitrary coefficient maps. The integral statement concerns ordinary ambient tensor throughout.

The item mathlib searches retain the inherited searches and append the queries actually run through `msearch.py`, with their actual hit names and directories from `searches.jsonl`. I read Point/Monoidal.lean and DerivedCategory/ExactFunctor.lean: underived monoidality and exact functor localization separately do not state the full item. A second semantic query likewise returned flat ordinary tensor lemmas, not this comparison. Broader point searches returned generic site-point constructions and ordinary stalks; the DAG search then located the exact existing geometric-stalk topos-point theorem. No service failure is recorded as a negative result.

## Not duplicates

No new nodes. The prospective general point-existence obligation is already `lem-fix-geometric-stalk-topos-point`; signed total tensor and scalar equations are already `lem-pur-cochain-pullback-tensor-coherence`; the exact resolving comparison is already `lem-pur-exact-pullback-signed-comparison`; total K-flat closure is already `lem-pur-kflat-total-tensor-model`. All are cited rather than recreated. I searched the whole DAG by titles, statements, tags and source labels, and used `blueprint_refs.py ancestor` and `search` (point tensor, sections exact, 07A4, 0993, geometric point, ringed evaluation, and geometric stalks are inverse images). No blueprint node states the full item in another form, so `same_as` remains empty.

## Review by N8

I read delivery-errors B--E in full, the three levels in SETUP, the stage-1 brief and stage document, GOAL, the worker role, the chapter and unit records, and the current blueprint relative-Kunneth proof and completed-coefficient definition. I checked the item against Stacks proetale.tex section-points (0991), including the paragraph constructing the point before lemma-classical-point (0993); sites-modules.tex lemma-tensor-product-pullback (03EL); and sites-cohomology.tex lemma-pullback-K-flat (0G7E), lemma-derived-base-change (06YY), lemma-tensor-product-K-flat (07A2), and lemma-pullback-tensor-product (07A4), including the total-complex construction. I read Bhatt--Scholze Lemmas 4.2.12 and 6.8.2(1) in the local PDF extraction for the finite/complete coefficient normalization. No prohibited SGA source is used.

For step 1 I read the whole statement of `lem-fix-geometric-stalk-topos-point`: it supplies the actual adjunction and preservation of finite limits, for the small pro-etale site and the same pointed colimit used here. The stalk definition specifies arrows and the opposite index; I verified explicitly that (s,id) is initial among neighbourhoods and hence terminal for the colimit. The displayed mutually inverse representative maps prove the claimed identification, so this is not an unsupported assertion that arbitrary pro-etale topoi are points.

For step 2 I checked that the general derived-pullback node explicitly defines ordinary module pullback by extension of scalars. Under the restriction identification the ring map is the identity and multiplication is the specified isomorphism. The exact-sections node explicitly covers arbitrary commutative ring sheaves and preservation of quasi-isomorphisms. No constant-coefficient restriction has been introduced.

For step 3 the cochain-coherence statement explicitly gives the isomorphism, its direct and inverse pure-tensor formulas, naturality and signed direct-sum totalization for arbitrary unbounded complexes. I checked its site hypotheses by using the chosen small pro-etale skeleton and the one-object site for ordinary modules in a common coefficient universe. The differential agrees summand by summand, and coefficients have degree zero. No sectionwise formula for an arbitrary sheaf tensor is assumed without this theorem.

For step 4 I read the general derived-pullback statement's flat-term K-flat preservation clause, the entire total-tensor model statement, and the exact-pullback statement including its eta normalization and representative square. These say exactly what is taken: the same resolving models, the same actual cochain comparison, and uniqueness/naturality of its descended transformation. The exactness hypothesis is established in step 2; closure of the source tensor is cited, not hidden. The exact-pullback theorem is an existing unsplit dependency, not a claimed finished Lean proof.

For steps 5 and 6 the cochain-coherence statement explicitly includes reassociation, signed symmetry, both action unitors, the compatible coefficient square, and composition of ringed pullbacks. I specialized its coefficient square to the point and checked that ring naturality gives the required square. I wrote both route values on generators: unsigned reassociation, (-1)^(ij) interchange, multiplication unitors, and the scalar product ab. For composed scalar maps the two multiplications agree by associativity; for identity maps they are the actual multiplication unitors. There is no assumption that B to B' is flat or invertible.

For step 7 I checked that the tensor-descent statement gives the resolving localization equivalence and natural representative maps. The general pullback node applies to coefficient extension on the identity topos, so it supplies K-flat flat-term representatives even for quotient maps. Total-tensor closure handles iterated tensors. The localization universal property explicitly preserves identities/composition of natural transformations and tests equality after localization; applying it successively to variables justifies passage from the actual chain equations to derived equations. All cited nodes were read by their statements, not by extracting unpromised constructions from proofs.

For step 8 I checked the DVR and finite-quotient hypotheses and used the pro-etale finite-constant-sections statement, not its etale-only counterparts. Its normalization explicitly identifies constant-presheaf elements with constant functions. Evaluation on the one-point space therefore gives the exact ring and quotient maps. For step 9 I checked that the inverse-limit definition explicitly includes ring sheaves and sectionwise coordinate projections. The compatible-residue argument is elementary from the cited completeness and valuation statements: the Cauchy bound gives existence, the closed-ball bounds give the prescribed residues, and the bound for every n gives uniqueness. It introduces no separate non-elementary completion theorem. This also proves normalization of every projection, rather than just an abstract ring isomorphism.

Edge cases checked: zero module or zero complex; the zero commutative ring sheaf; unbounded complexes with infinitely many direct-sum terms in a total degree; odd/odd degrees (the minus sign) and degree zero; the tensor unit; identity coefficient maps, a nonflat quotient map, and two successive quotient/scalar maps; n=1; and the compatible all-zero residue sequence. No constructibility, boundedness, field-coefficient, or flat-coefficient-map hypothesis was silently used. The coefficient formulas do not identify the completed coefficient sheaf with the discrete constant integral sheaf. Every non-elementary fact is in the statement of a cited node, the dependency union is exact, and a read-only closure traversal found no path back to the item from any proposed tool. Every proof step is below 2,000 characters (maximum 1,094). I corrected an initially mistyped source tag for tensor K-flat closure to the verified tag 07A2 before delivery.

Off-unit theorem uses are declared, with their purposes, in `split_report.tool_uses`; they are general point, cochain, localization or arithmetic tools, not replacements for a unit step. No maintainer fields were changed. `srvcheck.py ... review_split` passed with zero new nodes; it only noted that the unit has no realization recorded yet. The item is not the unit's key theorem, so this delivery does not write unit realization fields.

## Unfinished work

None within the one-level split. Existing unsplit dependencies remain queued for their own items. Final dry-run and push results are recorded below when available.
