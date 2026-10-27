# Worker report

Item: lem-trf-relation-incidence-open-model. Group Q16. Stage 1 only, 2026-10-22.

## Files written

- dag/nodes/sec-trace-formula/lem-trf-relation-incidence-open-model.json: existing statement node, now split into seven proof steps; no Mathlib match for the entire assertion.
- citations.json: eighteen verbatim cited-statement quotations, covering every uses entry in every proof step.
- report.md: this report.

No new nodes and no new Mathlib leaves. The sandbox also retains searches.jsonl and the local write_split.py preparation script. Those are research/preparation artifacts, not additional DAG files.

## Attachments

None. Searched the live read clone's lean/WeilConjectures by the exact blueprint tag and item id, and by incidence, relation/quotient, fppf relation, relation_incidence, restricted quotient and finding_opens concepts. The incidence hits describe generic-fibre component spreading; quotient/relation hits describe other algebraic or categorical quotients. No project declaration states this item with every clause, so there is no attachment claim. No Lean was written and no compiler or build was run.

## WANTED

None. All sources needed for the proof are present.

## What was wrong or changed

The existing node was statement-only, not a completed proof. Its statement is unchanged byte for byte. No statement dispute was found. The source's notation W=t(s^{-1}(g(U'))) is implemented by the incidence scheme E=U' x_U R and its image p(E), exactly as the item's statement requests. The proof avoids the misleading reading of the source sentence that g itself is surjective: only E to its image W must be surjective.

The statement dependency list and all inherited metadata, including the creation record and blueprint ancestry, are retained. The existing blueprint.from.place is already specified; same_as remains [] after the whole-blueprint searches. The new split_report identifies this as generic quotient-presentation support beneath the recorded ancestor, not a new claim about trace-class stalks. It is not the key node of sk-i-curve-zero, so no unit realization fields were changed.

The generic local-representatives theorem from another unit is declared in split_report.tool_uses. It is used solely for sheafification on the fppf site in Step 5, in a universe containing the site's objects and arrows. The unit's contracting-correspondence route is not replaced. The other off-unit geometric facts are existing Mathlib leaves.

## Searches and reuse

Read the item from the current shared repository and searched dag/nodes for the relevant Stacks tags and concepts. Read the full statements of every node cited in the proof. The first broad search found the ring-level finite-presentation permanence lemma; that statement alone does not assert scheme permanence, so it is not cited. Further searches found the exact existing scheme composition node lem-sbc-locally-finite-presentation-composition and clause (3) of lem-weil-pbc-qcqs-morphism-permanence, which do supply what Step 1 takes. This avoids a C4 error and avoids making another node for either fact.

Ran tools/blueprint_refs.py ancestor for the item and whole-blueprint searches for incidence, restricted quotient, finding opens, kernel pair, restricted fppf and finite presentation. The incidence hits are proper-coincidence and unrelated trace formulas. No blueprint node states the item in another form. The existing restricted etale quotient node has an etaleness hypothesis and is not a replacement for this flat/locally-finite-presentation assertion. The kernel-pair node has no etaleness hypothesis despite its id, and is the generic tool actually used in Step 5.

For the item, ran msearch.py with grep, LeanSearch, Loogle and LeanFinder, and a second LeanFinder phrasing. All five calls completed and their original records remain in searches.jsonl; each query is appended verbatim to mathlib_searches. LeanSearch/Loogle/LeanFinder return UniversallyOpen.of_flat and IsOpenImmersion.of_flat_of_mono, plus ringed-space coequalizer and scheme gluing results. Read the local Mathlib sources for these candidates. UniversallyOpen.of_flat supplies only openness (already the existing Mathlib leaf lem-weil-pbc-flat-lfp-open), and the flat-monomorphism theorem concerns an already given scheme morphism, not the quotient-sheaf incidence representation. The grep over AlgebraicGeometry for quotient.*relation|relation.*quotient|incidence has zero hits. No candidate states the entire item or specializes to it in one line.

## Not duplicates

No new nodes. Existing exact or more general tools were cited instead of duplicated: flat base change, flat composition, scheme local-finite-presentation composition and base change, universal openness, factorization through an open subscheme, fppf covering base change, local representatives of sheafification, and the relation kernel pair.

## Review by Q16

I read the item against Stacks spaces.tex Tag 02WU, lemma-finding-opens, especially the open-image construction and its final two paragraphs proving the representing property. I also read the supporting source statements in morphisms.tex: Tags 01TR/01TS (composition and base change of local finite presentation), 01U7/01U9 (composition and base change of flatness), and 01UA (universal openness); groupoids.tex Tag 045Y (local relation witnesses for equality in a quotient); sites.tex Tags 00WB/00WK (sheafification and local representatives); schemes.tex Tag 01HI (unique factorization to opens); and topologies.tex Tag 021O (fppf covering base change). The chapter and unit records, SETUP's three-level rule, GOAL.md, and the current main-20261015 ancestor statement/proof were read. The ancestor discusses contracting local terms; this auxiliary scheme/sheaf proof is used only through its recorded support ancestry. No SGA route is used.

Step 1 uses the flat-base-change node for pr_R, clause (3) of qcqs-morphism-permanence solely for local finite presentation under arbitrary base change, and the flat-compose and local-finite-presentation-composition nodes for t after pr_R. I read each statement: the qcqs hypotheses appearing in its earlier clauses are not imposed on clause (3). There is no assumption that E or U is quasi-compact or quasi-separated. This step proves p has both properties using g and t; it does not assume g is surjective.

Step 2 uses the universally-open leaf exactly for the image W. The open-factorization node gives p_W and uniqueness; the Cartesian-square argument is written out, so applying the same two base-change statements gives flatness and local finite presentation for E to W. Surjectivity is precisely the definition W=p(E). The cited fppf-site definition explicitly says that a jointly surjective flat locally-finitely-presented family covers, so the singleton is a covering. No unproved descent of scheme morphism properties is smuggled into the factorization.

Step 3 uses unique factorization through opens for va, the covering-base-change node for C=T x_W E to T, and the fibre-product definition for its coordinate equations. The relation section r equates the two quotient classes by the pointwise quotient definition; the canonical sheafification map preserves that equality. This gives a local F' section with the required image. This construction is the substantive forward direction of the item, not an application of a new node restating its clause.

Step 4 is an elementary use of the sheaf equalizer axiom, explicitly stated in def-weil-pbc-sites-and-cohomology. On C x_T C the two restrictions have identical alpha images; the item's injectivity hypothesis equates them. Gluing and separatedness give the global section and its image, and injectivity proves uniqueness. Thus citing a definition here really supplies the gluing axiom itself; it does not stand in for an uncited non-elementary theorem.

Step 5 uses the local-sections-of-sheafification statement to lift z_T to quotient classes on an fppf cover, and representatives of these classes give b_i. Its size convention is explicitly checked. The kernel-pair node states an isomorphism h_R to h_U x_F h_U for any monomorphic equivalence relation, so it provides actual r_i with both coordinate equations, not merely a full-faithfulness or definition assertion. The item's pointwise identification implies monicity; no etaleness is imported from the node's name. The fibre-product statement then supplies e_i into E.

Step 6 uses joint surjectivity from the covering definition to turn the images of va pi_i in W into the image condition va(T) in W. The open-factorization node now gives a genuine scheme map to W_V; this is valid for an open subscheme, and makes no analogous claim about closed or locally closed subschemes. Uniqueness of the two coordinates proves the two constructed maps inverse. This is a few-line elementary argument from the cited statements.

Step 7 checks both compatibilities rather than asserting that the construction transports: restriction changes (a,z) to (af,z restricted), and changing V by k changes its V coordinate to ka_1 while preserving z. The image of z is the same prescribed quotient section in either construction; alpha injectivity makes the F' coordinate unique. The unique factorization through the inverse-image open identifies the representing coordinate. This proves naturality in the test scheme and commutation with arbitrary base change V_1 to V over U.

I checked B1-B10: no new statement-only node needs a self-containment, definition, tag, Mathlib-leaf, duplicate or ancestry audit; searches were executed, recorded honestly and not invented, the existing statement is self-contained, and no Lean attachment was found. For C1-C8 I compared every uses entry to the actual statement and supplied the eighteen verbatim quotes; the only off-unit nonleaf generic tool is declared. In particular I corrected the initially considered ring-level permanence citation before writing the split. For D1-D5 the proof stays in the item, no assertion was moved to a restated child, no cycle is introduced by any new node, and the omitted sheaf gluing and naturality arguments are explicit. No non-elementary step exceeds 2000 characters.

For E1-E7 I checked g may have empty image, is not assumed surjective, and need not be etale; s,t are used only with the assumed flat/lfp properties. The site universe is large enough for the cited sheafification result. Small cases: U' empty gives E=W=empty, and a section on nonempty T would, by local representatives and joint surjectivity, force maps to empty; on empty T the sheaf axiom gives the unique section. If g is the identity, reflexivity supplies E=R mapping surjectively to U and W=U, and the representing map is the identity after the canonical quotient identification. With diagonal R and g an open immersion the conclusion is the usual inverse-image open. With diagonal R and a finite flat cover such as x maps to x squared, the restricted quotient still remembers equal images under g, so the conclusion represents the image, not the generally noninjective map h_U' to h_U. Arbitrary V and T empty are allowed throughout. These cases find no missing hypothesis and no source error.

No second worker was started: this is the direct-delivery self-review required by the brief. The maintainer's independent review remains the external reading.

## Unfinished work

None in the mathematical split. The first prescribed server dry run exited successfully with preflight passed at d6d02e36f54. Local consistency checks confirmed the statement is unchanged and proof_deps is exactly the union of the step uses. After correcting the report tag for flat composition from 01U8 to 01U7, the final dry run validates this report before the push.
