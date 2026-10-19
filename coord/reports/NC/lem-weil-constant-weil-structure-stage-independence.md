# Stage-1 worker report: lem-weil-constant-weil-structure-stage-independence

## Files written

- `dag/nodes/sec-smooth-purity/lem-weil-constant-weil-structure-stage-independence.json`: statement, split in eight steps; Mathlib verdict no match. Both original clauses and the original statement dependencies are preserved. The source, unit, ancestry, import flags and Lean-audit fields are preserved.
- `citations.json`: 29 verbatim statement excerpts, one for every step/node citation.
- `report.md`: this report. Supporting search results are logged in `searches.jsonl`; the local source extraction and authoring scripts are sandbox scratch material.

New nodes: 0. New Mathlib leaves: 0. No Lean files were written or compiled.

## Attachments

None. I searched the whole project source under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` by the exact item id, blueprint tag, stage-independence names and the constant-Weil/coefficient-stage notions, and inspected `WeilConjectures/WeilSheaf/Constant.lean`, especially lines 53–76. `AlgebraicGeometry.ProEtaleWeilSheaf.adicConstant` and `AlgebraicGeometry.WeilSheaf.adicConstant` construct the Qbar-l object but do not state the finite E-to-L compatibility or its common-stage consequence. The exact master source was also searched as reference material; it supplies no attachment for this item. A scalar-stage proposition in the slopmaster2 blueprint concerns multiplication of a morphism by a scalar, a different assertion.

## WANTED

None. The blueprint, Bhatt–Scholze PDF and Stacks sources needed for this argument are available locally. The proof is marked agent-written because the blueprint only names the canonical Weil datum, and does not prove this auxiliary stage-independence statement.

## Problems in the imported node and changes

The item was unsplit, with one inherited Mathlib grep search and no proof. Its statement is mathematically correct with the canonical, multiplication-normalized coefficient comparisons. I did not change it. In particular, I kept geometric Galois Frobenius, which is a scheme automorphism but generally not a k-morphism, and did not substitute absolute or relative Frobenius.

The completed integral coefficient ring is the inverse limit of the finite constant rings, not the discrete constant sheaf with value O_E. The proof distinguishes these throughout. The base-change comparison is the specified comparison for the derived-complete pullback/scalar-extension construction, not a map obtained by choosing unrelated derived-limit isomorphisms. Steps 3–6 compute it on the coefficient units using multiplication, quotient projections and the strict cone maps with zero shifted component.

I filled `blueprint.same_as` with an empty list after searches. The historical non-unspecified `from.place` and `via` remain unchanged. The current blueprint place is `main-20261015/blueprint/sec-six-functors-basics/sk-def-sf-admissible/def-weil-ordinary-compact-cohomology.md`, order 1869; its coefficient-object paragraph is the same intent as the inherited master source, order 1510. The inherited unit sk-def-sf-admissible is the admissibility-definition unit with no proof steps, rather than a unit theorem realized by this auxiliary item. No unit record or maintainer-owned binding was edited.

## Searches and reuse

Whole-DAG searches and `tools/blueprint_refs.py ancestor/search` were used for the full concept, canonical Weil structure, constant coefficients and scalar extension. I read the candidate statements rather than assuming that similarly named nodes gave the compatibility. The existing constant-coefficient lemma supplies the underlying scalar-unit isomorphism; it does not supply its Weil equivariance. The existing inverse-image theorem supplies naturality in coefficient homomorphisms; it does not itself prove the completed comparison square. Those are the calculations written in the item, not new clause-restatement nodes.

Six new searches were run through `msearch.py` and recorded verbatim: two LeanFinder phrasings, one Loogle pattern, one LeanSearch question and two grep patterns. All services returned results; none was recorded unavailable. LeanFinder's Frobenius hits were Witt-vector isocrystals, not l-adic sheaves. Its alternative phrasing returned general module/constant-sheaf/condensed functors. LeanSearch and Loogle returned constant-sheaf adjunctions and equivalence results. I read Mathlib `CategoryTheory/Sites/ConstantSheaf.lean` around `equivCommuteConstant` (142), its inverse (152) and `constantCommuteCompose` (184), and `AlgebraicGeometry/Sites/ElladicCohomology.lean` around `ellAdicSheaf` (63). These tools do not state completed finite-coefficient Weil compatibility or its common-stage consequence. No returned hit is an exact match or one-line specialization of this item.

## Not duplicates

No new nodes. All required inputs already exist and are reused.

## Review by NC

I read the item and both blueprint coefficient-object paragraphs, the chapter and inherited unit records, the full statement of every node cited by each step, Stacks `proetale.tex` Tag 09A5 (functoriality of the pro-etale site), `sites.tex` Tag 0H7J (constant sheaf mapping property), `sites-modules.tex` Tag 03EL (tensor product and pullback, including its adjunction argument), and `derived.tex` Tag 08TC (derived limit and its nonuniqueness warning). I also read Bhatt–Scholze Proposition 3.1.10 on page 17 and the surrounding repleteness discussion. The proof is an explicit agent argument using those constructions and the already stated DAG results; no SGA source is used.

Step 1 uses the Frobenius definition for the correct automorphism, the constant-Weil definition for the coefficient-unit datum, the pro-etale isomorphism theorem for exactness/limit preservation and naturality in all rings, and the completed-coefficient definition for the projections. All four statements say these things. The invertibility-of-l condition comes from the finite-field characteristic and l != p; no separatedness or k-linearity of g is needed by the inverse-image theorem.

Step 2 uses the exact same-index coefficient maps in the integral scalar-extension definition and naturality from the inverse-image theorem. I checked the action square after every projection, using the sectionwise limit definition, and wrote the resulting equality c_S F(j) = j c_R. This avoids the incorrect unramified-only identification of quotient rings. The calculation is an elementary composition of these stated maps.

Step 3 uses the definition of K-flatness and the sheaf tensor product to check the one-term regular module directly; no resolution theorem is being silently applied. The constant-coefficient lemma explicitly supplies constructibility, derived completeness and the underlying coefficient-extension isomorphism. The finite-free comparison theorem explicitly supplies the natural completion map chi, its invertibility and its quotient/zero-cone normalization. Thus beta = multiplication composed with chi inverse is the canonical unit map. I checked both its inverse and its finite quotient formula.

Step 4 uses the finite and strict integral pullback definitions for the actual representative, the isomorphism-derived-pullback statement for lambda, the canonical-Weil definition for theta, and clauses 2–3 of the surjective-tower result to identify the augmented limit map uniquely. I added the local lifting argument for epimorphy of the finite constant-sheaf transitions: a coefficient lifts through the ring quotient after choosing a local constant representative. The input is a tower of degree-zero sheaves and the source of the uniqueness assertion is also a degree-zero sheaf; I do not apply that uniqueness statement to an arbitrary complex.

Step 5 uses exactly the pure-tensor and scalar-extension clauses of the inverse-image/tensor theorem. The sheaf tensor definition justifies descending the local bilinear calculation. I verified the balancing relation against the coefficient-action square from Step 2, and calculated both maps as j(c_R(x)) c_S(y), including after every reduction. This is the argument establishing equivariance, not a citation to a new node repeating the item.

Step 6 uses the pullback part of the integral operation/scalar-extension theorem, whose hypotheses allow an arbitrary scheme morphism with l invertible, and the natural completion map from the finite-free theorem. R is derived complete and constructible by Step 3, and its pullback is in that category by the isomorphism theorem used in Step 4. The comparison is checked on quotient components and on both strict-cone coordinates; the zero shifted component is part of the stated finite-free comparison. Thus the passage to completed models preserves the actual square. This avoids claiming that reduction detects arbitrary derived morphisms or that cone lifts are uniquely determined in general.

Step 7 uses precisely the rationalization-on-representatives formula, the rational pullback formula, the definition of the canonical rational Weil maps, and the Weil-morphism equation. I checked the inverse equation by multiplication with alpha inverse and functoriality of pullback. Heart membership is stated in the constant-Weil definition. Thus all of clause 1, including an isomorphism of Weil sheaves, follows.

Step 8 uses the displayed common-stage Hom/representative construction and the finite-stage embedding of Weil pairs. The two explicit representatives compose to the identity at the same finite field. I checked the Frobenius equation at that field using the comparison already computed, the direction of the inverse, and the action of the forgetful functor on morphisms. Identity/tower coherence is part of the integral scalar-comparison statement; the multiplication formula also shows the normalization directly. No equivalence between fixed pairs and a derived category of Weil sheaves is assumed.

The three off-unit statement tools are declared in `split_report.tool_uses`: inverse-image/tensor compatibility, natural ordinary-to-completed scalar extension, and operation/scalar-extension compatibility. They are generic tools, and no step of the inherited unit is replaced by them. All other cited statements are in the item's unit; cited definitions are notions. The citation file was produced by extracting actual substrings from these statements and checked against every uses entry.

For edge cases, E=L gives multiplication as the unit identification, hence an identity equivariance square and an identity common-stage map. For Y empty the coefficient modules are zero and the same formulas give the unique isomorphisms, so no nonempty-scheme or nonzero-unit argument occurs. For Y_0 = Spec k_0 the structures give the usual trivial Frobenius on the coefficient line. In a ramified extension (for example adjoining a square root of l to Q_l), the maps A_{E,m} -> A_{L,m} need not be injective; the proof uses only their existence, their reduction compatibility and multiplication, and remains valid. Changing uniformizers does not identify their powers across fields. I also checked a tower Q_l subset E subset L: the two unit maps have the same product formula.

No non-elementary step exceeds 2000 characters. The non-elementary inputs are all stated existing nodes; the remaining inline calculations concern projections, multiplication, regular-module K-flatness, functoriality and inverse representatives. There are no new statements to audit for hidden clauses, duplicate tags or missing Mathlib searches. The server `review_split` check passed before report completion.

## Unfinished work

No mathematical part of this item remains unsplit. It is a stage-1 proof, not a claim that its dependencies have all been proved in Lean. Required delivery preflight and push are run after this report is written.
