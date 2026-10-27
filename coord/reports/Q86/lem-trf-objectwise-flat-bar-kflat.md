# Stage-1 delivery: lem-trf-objectwise-flat-bar-kflat

## Files written

- dag/nodes/sec-trace-formula/lem-trf-objectwise-flat-bar-kflat.json: existing statement, now split; no Mathlib match for the complete statement.
- citations.json: twelve verbatim statement quotations covering every use in the five proof steps.
- report.md and searches.jsonl: this report and actual search records.

New nodes: 0. New Mathlib leaves: 0. The statement and its statement dependencies are unchanged.

## Attachments

None. Searching WeilConjectures for the blueprint id and objectwise-flat / bar-K-flat terminology did not find a declaration proving all clauses. The general flat_presheafToSheaf_obj in CategoryTheory/GrothendieckAbelian/Monoidal/FlatResolution.lean supplies only a related flatness clause; bounded-flat and scalar-extension infrastructure do not alone state the entire item. This is not an attachment claim.

## WANTED

None. All sources used are in the read-only literature tree.

## Findings and corrections

The seeded item had no proof. It combined several valid assertions, not an exact Mathlib theorem. I retained its text and built a five-step argument without introducing any new nodes. I corrected the source description to name 06YQ (the actual sites-cohomology lemma-bounded-flat-K-flat tag) and 06YY for the scalar-extension comparison. The cited existing site-criterion node's source happens to say 06YS, but its statement is exactly the criterion needed; its source metadata is outside this item's edit scope.

The three blueprint levels and the chapter/unit records were read. This item is an auxiliary coefficient comparison several levels below lem-trf-local-term-locality. Its existing blueprint.from records the inherited nearby-cycle/semistable/cotangent coefficient-comparison branch; I preserve that ancestry and precise place. The current main-20261015 ancestor proof and the sk-i-curve-zero unit use the contraction/normal-cone route, not an internal-Hom stalk identification. The present work changes no geometric route. Searches of the whole blueprint for K-flat, flat presheaves and tensor colimits found no blueprint statement equal to this joint presheaf/bar model assertion, so same_as stays empty.

## Not duplicates

No new nodes are proposed. I reused lem-pc-sites-modules-coproduct-flat (03EU), lem-pc-bounded-above-flat-kflat-site (06YQ statement), the existing exactness leaf, lem-trf-derived-colimit-bar, and lem-pur-derived-change-of-rings. No duplicated special-case node is needed for ordinary modules: a one-object identity-cover site gives exactly that case.

## Mathlib searches

The item's five inherited 2026-10-22 records are retained as history. Five fresh searches were run through the required msearch.py command and are recorded exactly in searches.jsonl and mathlib_searches. LeanFinder's first query returned ordinary Module.Flat tensor-exactness criteria; its second formulation returned HomologicalComplex total-tensor infrastructure and Tor. LeanSearch returned scalar-extension exactness under flatness of the ring map, constructors for presheaves of modules and restriction-of-scalars descriptions. The ring-flat hypotheses would be additional here, and none of these hits asserts the combined bar/K-flat/scalar-comparison result. Loogle's Module.Flat, CochainComplex query and grep for flat bars/KFlat returned no hits. All services answered successfully. No unrun query or unavailable service is recorded as a negative search.

## Review by Q86

I read delivery-errors B through E in both copies, the standing worker brief, stage 1, GOAL, the three levels in SETUP, the chapter and unit records, and the current blueprint ancestor proof. For the mathematical source I read Stacks sites-modules section-presheaves-modules (03CS), section-tensor-product (03EK), definition-flat (03ER), lemma-colimits-flat (03EU), and sites-cohomology example-left-derived-colimits (08PG), lemma-bounded-flat-K-flat (06YQ), the construction preceding definition-derived-tor (06YU) and lemma-derived-base-change (06YY). There are no new nodes needing an additional source review. The proof is marked agent assembly because this exact joint assertion is extracted from the parent comparison, rather than copied from a single numbered source theorem.

For step 1 I opened all four cited statements. The bar node explicitly states that every presheaf is a sheaf for the identity-cover topology; the tensor definition explicitly gives sectionwise tensor followed by sheafification. Since the inclusion is now the identity, so is its reflector. The exactness leaf states that kernels, cokernels and images are sectionwise. These allow short exactness to be detected object by object. The hypothesis on each F(U) is explicitly preservation of short exact sequences, exactly what this step uses. The final cited definition defines flatness by exact sheaf tensor, not by an unstated stalk criterion. This is a few-line elementary application of those statements, not a separate flat-presheaf node.

For step 2 I checked the complete statement of the site criterion: arbitrary ringed site, bounded above and flat terms. F[0] has bound zero; its sole possibly nonzero term was proved tensor-flat in step 1. Zero terms are flat directly. The K-flat definition cited here uses acyclicity of the direct-sum total tensor, so the conclusion matches precisely, without changing the K-flat convention to an unmentioned projective notion.

For step 3 I checked the bar statement's degree formula and the full coproduct-flat and site-K-flat statements. Smallness makes the set of composable n-strings small in the same universe, so the coproduct hypothesis holds even with infinitely many objects or loops. On the category with one object and only its identity, all sheaf data is a single R-module and sheaf tensor is module tensor. Thus the coproduct theorem applies to the flat F(U_0), not to representable presheaves or to the non-flat algebra S. Positive terms are zero and the resulting bar has upper bound zero, independently of its possibly infinite negative tail. The site criterion then yields its ordinary-module K-flatness. No spectral-sequence convergence or unproved finite-boundedness assertion is hidden in this step.

For step 4 I read the entire statement of derived change of rings, especially clause (2)'s canonical comparison for every K-flat resolution. The identities of the two complexes are quasi-isomorphisms and K-flat resolutions by steps 2 and 3. On the original site the map is the constant ring-sheaf map; on the one-object site it is the ordinary ring map R to S. The output is in D(S) in the latter application and D(underline S) in the former, not merely after forgetting the S-action. Termwise extension of a degree-zero complex gives the displayed degree-zero module sheaf by definition. Using these identity resolutions pins the maps to the canonical comparisons of the statement, and does not assume S flat over R. Both sources actually have flat terms too, so even the explicit flat-term form of source Tag 06YY applies.

For step 5 I reread the bar node's derived representation and the scalar-extension node's functor clause. Applying that functor to the representation gives exactly the required identification of the second source. This is elementary functoriality and requires no additional coefficient base-change theorem. It does not reprove the bar representation or take an assertion from that node's proof instead of its statement.

The three nonclosed off-unit generic tools are declared in split_report.tool_uses: coproduct flatness, bounded-above flat K-flatness, and derived change of rings. They are coefficient-category tools, not a replacement of a geometric unit step. The exactness node is already a Mathlib leaf. All cited node statements were checked against citations.json, and their quotations are literal substrings. No new definition, hollow construction, changed target, SGA reference or Lean file is involved. Every proof step is shorter than 2000 characters; the proof has no concealed long comparison argument. B's new-node conditions are vacuous; C1 and C4 were checked by the per-step analysis above; D is satisfied by the actual pointwise argument and applications rather than moving clauses into fresh nodes; E's hypotheses and objects were checked as described.

I tested the empty category and F=0 (all complexes zero), the singleton category with F=R and R to R/I nonflat (ordinary scalar extension is still computed by the flat source), and a category with arbitrarily long strings from identity or nontrivial endomorphisms (the bar is unbounded below but still bounded above). These check the size, bound, zero-term and absence-of-flatness-of-S claims. No statement dispute arose.

## Dry-run repair

The first local citation gate required at least forty characters for the flat-sheaf definition quote. I replaced the short phrase with that node's entire verbatim statement; no proof or statement change was needed.

## Unfinished work

None in the stage-1 split. Independent mathematical review belongs to the maintainer; this is the author's self-review.
