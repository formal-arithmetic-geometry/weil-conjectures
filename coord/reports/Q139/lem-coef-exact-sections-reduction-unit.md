# Q139 — lem-coef-exact-sections-reduction-unit

## Files written

- `dag/nodes/sec-six-functors/lem-coef-exact-sections-reduction-unit.json`: statement, now split into seven proof steps. No statement change, no new nodes, no new Mathlib leaves. Prior searches and all original metadata are retained; eight searches actually run for this delivery are appended.
- `citations.json`: one verbatim statement quotation for every step/node citation (15 entries).
- `report.md`: this report.
- `searches.jsonl`: actual search-command records; `write_split.py`: sandbox-only construction of the item and citation records.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and for exact-section, quotient, reduction and scalar-unit terminology. No project declaration states all clauses for arbitrary small sites and arbitrary commutative coefficient rings. In particular, `exists_derivedTensorHom_sections_unit` is about the derived tensor-Hom unit and zeroth hypercohomology, not this coefficient-reduction comparison; the adic completion-unit declarations have different objects and hypotheses. No Lean was written or compiled.

## WANTED

None: all sources used here are present locally.

## What needed work

The item was statement-only. It already explicitly distinguishes ordinary module K-flatness from sheaf K-flatness and asks for the actual adjunction unit, so neither distinction may be suppressed. The existing sheaf-resolution-independence node gives the canonical map and coherence but explicitly does not assert invertibility. The existing flat-comparison and natural-comparison nodes assume that R is a domain and t is nonzero; the current item's weaker nonzerodivisor hypothesis does not permit citing those conclusions. I instead use the already existing principal-quotient quasi-isomorphism theorem after separately checking termwise injectivity on the section complex and its ordinary flat-term replacement. No statement dispute, weakening, new hypothesis or change of coefficient category is required.

The proof is an agent extraction, marked as such, of the principal-quotient comparison and normalized adjunction argument. Stacks 06YY and 07A6 are the derived-extension/adjunction sources, not a claim that those tags literally state the full exact-sections result.

## Not duplicates

No new nodes were created. DAG searches by 06YY, 07A6, 0FND and by quotient/sections terminology found the existing tools that the proof uses. Whole-blueprint searches `exact sections`, `principal quotient`, and `scalar-extension unit` found only the w-contractible exact-sections theorem for the first query and no matches for the other two. That theorem supplies exactness in a geometric special case and does not state this derived comparison. The item's `same_as` remains empty.

The closest existing nodes are `lem-pod-derived-reduction-sheaf-resolution-independence` (comparison and resolution coherence, no isomorphism or normalized-unit assertion), `lem-pod-principal-reduction-flat-comparison` and `lem-pod-principal-reduction-comparison` (domain hypothesis and no displayed normalized-unit formula). None replaces the whole item. Their more general ingredients are reused instead of copied into new nodes.

## Review by Q139

I read the worker brief, stage-1 contract, SETUP's three levels, GOAL, the chapter and unit records, and both occurrences of delivery-errors B–E. The item serves the third mapping-complex comparison and final natural-map identification in paragraph 2 of `prop-coef-integral-dualizing`: I read its current 20261015 statement and proof, including the requirement that finite-level counit-defined comparisons identify the specified maps before limits. This split stays below that unit route. It does not use any prohibited SGA source; inherited chapter/unit bibliographical text was not used as proof input or modified.

For the mathematical source I read Stacks `sites-cohomology.tex` at lemma-K-flat-resolution (06YS), lemma-derived-base-change (06YY), and lemma-adjoint (07A6); `more-algebra.tex` at lemma-K-flat-resolution (06Y4); `derived.tex` at lemma-pre-derived-adjoint-functors-general (0FND); and `algebra.tex` at definition-flat and lemma-flat (00HB/00HD). The principal-quotient preservation fact is already a DAG node: I read its complete statement and its existing Lean module's short-exact-sequence explanation. No proof of a cited node is being treated as a stronger statement. I also read the normalized coefficient-adjunction statement in full and its module's description of the universal counit normalization.

Step 1 uses the sheaf-module, restriction-of-scalars and derived-category definitions. Their statements give the same underlying abelian sheaf, the coefficient action and localization. The assumed exactness of sections, applied to cycles and boundaries, is the entire argument for preservation of quasi-isomorphisms; there is no implicit cohomological acyclicity theorem. Compatibility of the two coefficient maps ensures that the two restricted section targets agree as R-modules as well as as abelian groups.

Step 2 cites the sheaf flat-term K-flat resolution theorem, the definition of flat sheaves and the existing sheaf-resolution-independence comparison. I checked that each statement introduces the same small ringed site and allows unbounded complexes. Exact tensoring is the definition of flatness here, so the proof writes out its application to the assumed short exact coefficient sequence. Global sections preserve the resulting monomorphism, hence C=Gamma(P) is termwise t-regular. The comparison node states theta, beta, naturality on chain maps, and the exact transported equality for two resolutions; it does not state invertibility, and this step does not take invertibility from it.

Step 3 uses the ordinary-module resolution theorem, flat tensor exactness, the universal mixed-tensor counit and the fixed-second-factor derived tensor construction. The first gives flat terms as well as K-flatness, even for unbounded C; categorical flatness agrees with module flatness in its statement. The flat tensor theorem explicitly includes preservation of injections, so it applies to t:R to R. The counit is a natural transformation at arbitrary complexes, not merely at K-flat ones. Its naturality gives c_C L(q)=Q(bar q)c_Q. The fixed-second-factor theorem identifies the chosen L and its canonical K-flat computations. Thus the chain formula comes from the actual counit. C itself is never asserted K-flat.

Step 4 cites `lem-pod-principal-quotient-quasi-iso`. Its hypotheses are exactly a surjection with kernel tR, a quasi-isomorphism q, and termwise t-injectivity on both source and target. These were checked in steps 2–3. It does not require a domain, boundedness or flatness of the target. It produces the needed quasi-isomorphism in A-module complexes. Localization then proves invertibility of c_C and beta_P. This avoids inferring that a plain isomorphism of cones has the requested normalization.

Step 5 uses precisely clauses (1) and (2) of the normalized sheaf coefficient-adjunction statement. Its arbitrary-small-site generality allows the one-object site, where a module sheaf is simply a module and sections are identity; this is the ordinary-module adjunction with the specified normalization. The ordinary resolution Q has both flat terms and K-flatness, as that statement requires. On the sheaf side P has the corresponding two properties. I wrote the equality after precomposition with Q(q) and checked its section formula before cancellation. The explicit formula x to q(x) modulo t is exactly the localized ordinary transpose. This proves the required unit normalization without assuming that Gamma(P) is a valid K-flat computing object.

Step 6 uses the actual resolution-independence equality and the adjunction bijection from the two cited statements. Both G(p) and LG(p) are invertible because p is a quasi-isomorphism and G preserves these. The displayed calculation transports the unit equation with the correct restriction of T(p). Uniqueness follows from the adjunction hom-set bijection. For arbitrary derived f I wrote the two adjuncts and equated them using naturality of v; thus naturality is not limited to morphisms admitting the same chain representative. Step 7 is an elementary consequence of the intrinsic counit in step 3 and the transported equality in step 6, giving independence of both resolutions and of the adjunct. Every cited statement has a literal quotation in citations.json.

I tested the statement against the point site with O=R=Z, t=2, both N=Z[0] and N=(Z/2)[0]. The second case has derived reduction in two degrees; the proof uses the flat resolution and does not collapse it to the underived quotient. If t is a unit, A and O' are zero and both comparison targets vanish. If R is the zero ring, unital coefficient maps force O and O' to be zero, so the statement is still consistent. A product ring such as Z times Z with t=(2,3) is allowed and verifies why the domain-only comparison lemmas were not used. No boundedness, finite generation, noetherianity, enough-points hypothesis or flatness of the coefficient map R to Gamma(O) appears in the argument.

For B–E specifically: there are no new statements to be non-self-contained or duplicates; mathematical notation is encoded once; source labels/tags are stated; all searches appended to the node were actually run with msearch.py and their hits read. The hits concern ordinary tensor exactness, ordinary change of rings, global sections or abstract localization, not this normalized derived sheaf comparison. Definitions are used only for their stated content, each substantive lemma has its own existing citation, and no new node merely restates a clause. All steps are shorter than 2000 characters. The supplied statement and metadata are retained, and generic off-unit tools are declared in split_report.tool_uses for the maintainer's review.

## What could not be finished

Nothing mathematical remains in this one-level stage-1 split. Server dry run and delivery are recorded below after they finish.

## Validation

The required server dry run exited successfully: `OK (not pushed) deliver/Q139/lem-coef-exact-sections-reduction-unit at dd6bd31c2e8: preflight passed`. The item and citations were unchanged after that check; this report records its result. The push is performed with the required delivery tool, which runs its own admission and preflight checks.
