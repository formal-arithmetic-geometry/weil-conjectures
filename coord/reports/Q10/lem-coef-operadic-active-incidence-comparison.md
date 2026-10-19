# Worker report: lem-coef-operadic-active-incidence-comparison

## Files written

- `dag/nodes/sec-six-functors/lem-coef-operadic-active-incidence-comparison.json` — existing item copied into the Q10 sandbox, status set to `split`; no new DAG nodes.
- `citations.json` — 19 entries, one for every cited node in every proof step, with verbatim statement quotes.
- `report.md` — this report.

## Attachments

No finished declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` states this item. No attachment is claimed.

## WANTED

- Lurie, *Higher Algebra*, Theorem 3.1.2.3, step (1), printed pp. 336–337 (the active-part coslice comparison, first-vertex restriction, and output-product comparison); the PDF was read online but is not archived under `literature/`.
- Gepner–Haugseng, *Enriched Infinity-Categories via Nonsymmetric Infinity-Operads*, arXiv:1312.3178v4, Appendix A (generalized nonsymmetric incidence diagrams and endpoint convention); read online but not archived under `literature/`.
- Lurie, *Higher Topos Theory*, §§2.1.2 and 4.1.3 (relative join-coslice and pointwise-adjoint orientation); read online/against the cited interfaces, not archived under `literature/`.

## Not duplicates

No new nodes were created. The existing symmetric analogue `lem-coef-symmetric-family-active-slice-calculus` was checked and does not state the nonsymmetric family, endpoint-incidence, or parameter-simplex comparison in this item.

## What I checked and corrected

The source item, its unit `dag/units/sk-prop-sf-biduality-general.json`, chapter `dag/chapters/sec-six-functors.json`, and the stage-1 contract were read. The upstream source trees contain no declaration tagged `(blueprint: lem-coef-operadic-active-incidence-comparison)` and no declaration with this statement. The item is a genuine infinity-categorical lemma rather than a Mathlib result. The blueprint ancestry is `prop-coef-integral-exceptional-adjoint`, proof paragraph 2, where the operadic Kan-extension construction needs active incidence and comma-cone comparisons. The item’s hypotheses were retained exactly, including constant parameter-zero restrictions, space-valued zero fibers, and the stronger requirement that stationary inert lifts are cocartesian for the whole family projection.

Step 1 proves the product decomposition of `J_b`. I read the full statements of `def-coef-operadic-correspondence`, `lem-coef-infinity-cocartesian-mapping-criterion`, and `lem-cbc-enhanced-functor-cone-calculus`; they provide respectively the incidence/Segal relative-limit axiom, the mapping-space characterization of cocartesian factorization, and coherent functor/cone mapping-space calculus. The proof explicitly cuts along consecutive inert restrictions, glues endpoint lifts through the contractible space fibers, and uses the global (rather than merely fiberwise) cocartesian hypothesis across the parameter edge. It checks arity-changing source morphisms and coherent triangles, so the result is an equivalence of source categories, not only an equivalence of operation spaces.

Step 2 identifies the active source part with the source-restricted join slice. I checked `def-coef-operadic-correspondence`, `def-cbc-enhanced-diagrams-cones`, `lem-coef-initial-poset-slice-restriction`, and `def-cbc-enhanced-diagrams-cones`’s quasicategory/space conventions. The proof verifies that active edges form the required full subcategory and that a source edge between active cones is active by the endpoint-preserving opposite ordinal calculation. The least element is the first vertex of the simplex, and the cited restriction lemma supplies all boundary lifts, including dimension zero; no nonemptiness assumption is inserted.

Step 3 constructs the active reflector and applies the relative right-coslice restriction theorem. I read the statements of `def-coef-operadic-correspondence`, `def-coef-monoidal-infinity-category`, `lem-coef-infinity-slice-right-fibration`, `lem-coef-infinity-cocartesian-mapping-criterion`, `lem-cbc-right-fibration-morphism-space`, `lem-coef-infinity-pointwise-adjoint-criterion`, and `lem-coef-cofinal-relative-join-slice-restriction`. The interval factorization is made explicit: a mixed base map factors through its inert interval, the stationary global cocartesian lift gives the unit to an active cone, and endpoint preservation forces every map into an active cone to factor through that lift. The right-fibration mapping-space statement passes this factorization to coherent cone triangles; the pointwise criterion assembles the reflector; the relative join-coslice lemma then gives exactly the displayed trivial Kan fibration over `Delta^op`, with base and active restriction fixed.

Step 4 checks compatibility with source diagrams and induced cones. I read `def-coef-monoidal-infinity-category`, `def-coef-operadic-correspondence`, and `lem-cbc-enhanced-functor-cone-calculus`. Segal coordinates send a tuple to the ordered concatenation of the coordinates of its inert restrictions, shared endpoints land in the arity-zero fiber, and the relative mapping-space product identifies cones and all coherent parameter simplices. This checks the hypotheses on inert projections and the naturality of the specified restriction maps.

Step 5 checks edge cases. For zero outputs, an active map to `[0]` forces source arity zero, so `J_b` is the contractible zero-fiber slice and the source diagram is empty. The one-block case gives identity comparisons; dimension-zero first-vertex restriction is the identity; an empty target slice forces both active and full source slices empty, reducing the coslice comparison to an identity. These checks use only the stated operadic, monoidal, and relative-cone definitions and do not assume colimits in `V^tensor`.

I searched the whole DAG and blueprint for this statement and for active/incidence/slice keywords; no duplicate statement was found. I ran Q10 `leansearch`, `leanfinder`, `loogle`, and `grep` searches in `searches.jsonl`; all returned no relevant Mathlib declaration (the only grep hit was a commented tactic name in `Mathlib/Tactic/CategoryTheory/Slice.lean`). The item’s recorded search history was preserved and the exact Q10 searches appended. I tested the split’s edge cases `r=0`, `r=1`, `r=2` with shared endpoints, `d=0`, and an empty `J_{sigma(0)}`. No statement correction was needed, and no SGA source was used.

## Review by Q10

I independently read the item statement, all five proof steps, the unit and chapter records, and every cited node listed in `citations.json`. Each citation quote is copied verbatim from the cited node’s statement. I verified the global stationary-cocartesian hypothesis at the two places where the argument crosses the parameter edge: the cutting/factorization construction in step 1 and the active reflector in step 3. I checked the least-element hypothesis for step 2, the inner-fibration and mapping-space hypotheses for step 3, and the monoidal Segal and arity-zero conditions for step 4. The small cases listed above validate the zero-arity, one-block, endpoint-sharing, dimension-zero, and empty-source clauses. The only correction made in the sandbox was marking the already complete five-step split `status` as `split` and adding the exact current Q10 search records; the statement, proof, dependencies, blueprint ancestry, and prior review fields were retained.
