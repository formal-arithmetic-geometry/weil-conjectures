## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-hypercover-normalized-single-site-descent.json`: statement, split; no exact Mathlib match. Nine proof steps reuse existing DAG nodes and explicitly calculate all normalization identities.
- `citations.json`: 22 verbatim full-statement quotations for the 22 step/node citation pairs.
- No new nodes, no Mathlib leaves, no Lean files and no unit changes.

## Attachments

None. Searches of the project under `lean/WeilConjectures/` for the item tag, hypercover descent and normalization, weak contractibility, and signed homotopies found no declaration stating all the clauses. Weak-contractibility and injective-resolution infrastructure covers parts, not an attachment for this item. No compiler was run.

## WANTED

None. The sources needed for this split are available locally.

## Corrections and route

The imported statement is retained exactly. It has no proof or Lean audit attachment. No released repair note exists. The sandbox initially contained only searches.jsonl and dispatcher markers; there was no earlier split or report to discard. The six existing sandbox searches were reused, without repeating the queries; their actual logged tools, queries, counts and results are added to the inherited Mathlib search record. Relevant injective-resolution hits were checked in Mathlib's CategoryTheory/Abelian/Injective/Resolution.lean (iso_hom_naturality) and Algebra/Homology/DerivedCategory/RightDerivedFunctorPlus.lean: these supply resolution/derived-unit infrastructure but do not state the signed section total on this ringed site or all its normalization clauses. The other grep hits concern truncated hypercovers. Dold--Kan/alternating-complex homotopies do not state this coefficient-total formula. No new leaf is asserted from those hits.

Read the chapter record and sk-thm-sf-ctf-stability unit. This is a descendant supporting the open-direct-image calculation, not the key statement of that unit. The inherited blueprint place and via chain are retained. `blueprint_refs.py ancestor` returns None for this imported created-item chain; I have not invented an ancestor. Whole-blueprint searches for hypercover and contractible found the existing compute-cohomology nodes, but none stating all the every-resolution, signed-homotopy and refinement assertions here. The proof follows the two filtrations of Tag 09A2 and adds explicit normalization algebra, without changing the unit route. Generic off-unit tools are declared in split_report.tool_uses for independent maintainer review.

The main C4 trap was that det-pe-wc-sections-exact assumes an affine spectrum of a w-contractible ring: the item has only categorical weak contractibility. Step 1 instead cites the existing proetale-weakly-contractible-evaluation-exact node, whose statement uses exactly set-sheaf epi surjectivity and preserves module homology. The main coefficient trap was forgetting injectivity: the proof uses a theorem for injective module sheaves, never an assertion that their underlying abelian sheaves are injective. I also avoided using the etale constant-ring enough-injectives node for a variable pro-etale ring sheaf. The general ring-sheaves-grothendieck node is the appropriate universe-compatible structural input.

## Unfinished work

None in this stage-1 split. Existing cited unsplit theorems remain their owners' work; this delivery introduces no statement-only sublemmas.

## Not duplicates

No new nodes. Existing results are cited instead of duplicating them. In particular, the exact evaluation, total column comparison, module injective row, row-to-total comparison, and K-injective comparison were all already present. No new-node/existing-node same-tag pairs arise.

## Review by Q45

I read Stacks proetale.tex, Tag 09A2 (lemma-compute-cohomology), including both the column and row arguments, sites-cohomology.tex Tag 0946 (lemma-w-contractible), hypercovering.tex Tags 01GE (lemma-acyclic-hypercover-sheaves) and 01GW (lemma-injective-trivial-cech), and homology.tex lemma-first-quadrant-ss and lemma-double-complex-gives-resolution. For the resolution comparisons I read derived.tex Tags 013R (lemma-acyclic-is-zero), 013P (lemma-morphisms-lift), 070I (lemma-K-injective), 070J (lemma-bounded-below-injectives-K-injective), 070Y (lemma-K-injective-defined), and 070K (lemma-enough-K-injectives-implies). The normalization, signed homotopy and refinement equations are my explicit additions, so proof_origin is agent. No prohibited SGA source is used. There are no new nodes requiring a separate source review.

I opened and read the statement of every cited node. Step 1 takes preservation of homology from proetale-weakly-contractible-evaluation-exact under exactly the set-sheaf hypothesis in the item; homology preservation gives both exactness and preservation of coefficient quasi-isomorphisms. Step 2 uses bounded-below-total-column-comparison with common bounds 0 and min of the two coefficient bounds; its statement requires these bounds and column quasi-isomorphisms, both checked. The total definition gives precisely the differential used, so no unsigned flip is being silently substituted.

In step 3, proetale-subcanonical says the representables are sheaves, proper-face-matching-arrow supplies limits in the slice (degree zero W, degree one the product there), and site-sheaf-sets-epi-locally-surjective supplies the equivalence between local lifts and epimorphisms. A compatible test boundary therefore maps into the matching object and lifts after pulling back its covering arrow. The ringed-hypercover-injective-augmentation statement explicitly permits these represented matching epimorphisms and an injective module sheaf over an arbitrary commutative ring sheaf. Its displayed restriction augmentation, not just an abstract cohomology isomorphism, is what step 3 uses. Step 4 uses exactly the hypothesis and conclusion of proetale-hypercover-injective-complex-comparison, with the actual map fixed by the augmentation definition.

Step 5 is a direct calculation from the signed total definition and the homotopy equation in def-pur-kinjective-complex. At p and p+1 the two horizontal signs cancel; the two vertical signs multiply to +1. I checked that H decreases q, not p. The localization definition explicitly allows the homotopy-category presentation, so equality after Q follows. This step is elementary algebra, not an uncited total-homotopy theorem.

Step 6 uses ring-sheaves-grothendieck on the small site in the stated coefficient universe and kinjective-computes with its identity functor, giving K-injectivity of both bounded-below injective complexes. The comparison principle then gives k with ki homotopic to i' even when the resolutions are arbitrary quasi-isomorphisms rather than monomorphisms. The right-derived-functor definition includes the unit and its invertibility on K-injectives. The displayed formula rho_i = eta_I inverse composed with RGamma(Qi), followed by unit naturality, proves the specified evaluation normalization without relying on the proof of any other node. Step 7 explicitly cancels the invertible actual total comparison to prove independence and the every-resolution identity. Step 8 applies the same comparison principle to j f and writes out the three equations needed for coefficient naturality, so no strict comparison square is assumed.

Step 9 checks restrictions on individual summands; simplicial compatibility gives the horizontal chain equation and coefficient restrictions give the vertical one. The two strict augmentation/resolution squares are then used in the displayed cancellation equation proving refinement compatibility. Identity and composition laws are componentwise restriction laws. For M[0], q=0 is the only surviving coefficient degree and the stated alternating differential follows directly. This is elementary from the cited total and augmentation definitions, not an additional descent theorem.

I checked delivery-errors B--E point by point: no new nodes or hidden proof sketches, no definition-only citation standing in for a non-elementary theorem, all citation quotes are literal substrings of their nodes' statements, no use of another node's proof, no ancestor/descendant cycle introduced, and no unsupported affineness, constant-ring, boundedness or injectivity assumption. All proof steps are below 2000 characters. Small-case checks include the zero complex and zero coefficient ring, lower bound N negative, the empty base, identity refinements, and degree-zero coefficients. In each case finite diagonals and the same restriction equations remain valid. For a constant hypercover over a weakly contractible W, the alternating row has the expected degree-zero augmentation and no extra positive cohomology, consistent with the formula. The sign cancellation was also checked at p=0 and p=1. No statement dispute was needed.

## Validation

The first dry run rejected two total-definition quotes as shorter than 40 characters. I replaced the citation excerpts by their full cited statements, preserving exact text and all hypotheses. No mathematical change was required.
