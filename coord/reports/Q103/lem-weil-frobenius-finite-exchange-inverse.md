# Stage-1 report: lem-weil-frobenius-finite-exchange-inverse

## Files written

- dag/nodes/sec-six-functors/lem-weil-frobenius-finite-exchange-inverse.json: statement, split; no exact Mathlib match. Four steps, using only existing nodes.
- citations.json: verbatim statement excerpts for every step/node citation.
- report.md: this report. No new nodes or Mathlib leaves.

## Attachments

None for this item. Searching the project by its blueprint tag, Frobenius exchange, transport and finite-coefficient terminology found underived Frobenius comparison isomorphisms in WeilConjectures/SixFunctors/ProEtale/GeometricFrobenius.lean, but these do not state the specified ambient unbounded derived mate, the chosen compactification composite, and the transported inverse formula together. They are not an attachment for this item. Existing derived-pullback equivalence and mate-invertibility nodes supply the needed interfaces.

## WANTED

None. The source PDF, Stacks sources and relevant blueprint material are available locally. Deligne motivates transport; the stronger ambient pro-etale verification is explicitly agent-written.

## Corrections and source comparison

The statement is unchanged, including all unbounded, semilinear and non-separated-ambient-scheme clauses and the limited etale-origin domain for changing compactification. The imported item had no proof. Its statement dependencies are retained because they introduce precisely its data, operations, witnesses and specified comparisons. No blueprint update or released repair order is present. The source's motivating transport assertion does not itself prove the full ambient derived assertion; the proof therefore has proof_origin.by = agent rather than attributing that stronger result to Deligne.

The whole-DAG statement/title searches and blueprint_refs searches for mate, Frobenius, Frobenius exchange and FrEx found the existing lem-weil-isomorphism-derived-pullback-equivalence, lem-weil-mate-iso-along-equivalences, lem-trf-open-square-exchange and the Cartesian-square nodes. No additional lemma is needed. The abstract mate step is an application of the existing node, not an assertion that every invertible square has an invertible mate. Mathlib searches were run through msearch.py, read, logged and appended without changing the item's inherited searches. The second semantic phrasing found CatCommSq horizontal/vertical inversions and categorical pullback equivalences, which do not state this pro-etale derived mate assertion. The first semantic query, LeanSearch and source grep also yielded no exact match.

## Unfinished work

None at stage 1. No Lean file was written and no compiler, Lake or local DAG/preflight checker was run.

## Not duplicates

No new nodes: all supporting statements already exist and are cited directly.

## Review by Q103

I read Deligne, Weil II, printed pages 150-153, (1.1.7), (1.1.10)-(1.1.11), (1.1.14), from the local PDF, and the ancestor blueprint's global-geometric-Frobenius definition. The former distinguishes arithmetic substitution from its geometric inverse and describes transport of structure, including compact cohomology. I read the item's chapter and inherited unit: this auxiliary transport verification realizes the ancestor's first cohomology arrows, and does not substitute another route for a unit theorem. No unit realized fields are changed because this item is not that unit's key statement.

For step 1 I opened the complete statements of lem-weil-frobenius-square-cartesian and lem-weil-isomorphism-derived-pullback-equivalence. The first gives scheme isomorphisms, commutation and the Cartesian square for arbitrary k_0-morphisms, without requiring k-linearity or separated schemes. The second explicitly gives equivalences on the ambient unbounded derived module categories at A_{E,n}, not merely on constructible objects. The coefficients agree with the item's A_n and ell is invertible since the schemes have characteristic p distinct from ell. Applying these to p_0 is legitimate for the supplied compactification over k_0, so its geometric Frobenius is covered too.

For step 2 I read the full statement of lem-weil-mate-iso-along-equivalences and item 1 of def-weil-frobenius-square-exchange. Its left adjoints are the two copies of Lf^*, its side functors are Lg_Y^* and Lg_X^*, and its theta is exactly the specified pullback-compositor square. Thus its explicit unit--theta--counit formula is the requested arrow, rather than an unspecified isomorphism between its endpoints. Step 1 supplies an equivalence for the first side and full faithfulness for the second, exactly the hypotheses the abstract node states. The argument for p uses the identical substitution. I checked the ambient ringed-exchange definition as well to confirm the orientation of theta and the adjunctions.

For step 3 I read lem-trf-frobenius-open-square and lem-trf-open-square-exchange completely. Their statements respectively supply the Cartesian square of the open immersion and its canonical pro-etale derived b, natural in its argument, with no properness of f required. I also read Stacks Tag 03S6, etale-cohomology.tex, lemma-shriek-base-change: it states extension-by-zero base change on abelian sheaves and modules, motivating the existing derived pro-etale node; I have not applied the etale statement directly to pro-etale complexes. Item 2 of def-weil-frobenius-square-exchange specifies precisely the same composite ve. Applying Rp_* to b^{-1} and multiplying the two composites gives both inverse identities by associativity and cancellation. These elementary cancellations are written in the step and are not made into extra nodes. Naturality follows from the specified natural transformations, not a pointwise choice of inverse.

For step 4 I read the finite-level paragraph of def-weil-derived-pullback-tensor-hom, all of lem-weil-pbc-comparison-pullback, and the domain restriction of prop-compactification-coherence-detailed. I also read Stacks Tag 09A5, proetale.tex, section-morphism, which writes the inverse-image comparison square explicitly. Exact termwise inverse image preserves the lower bound on L, giving a witness for the pulled-back object. Consequently both comparison components used really lie in the comparison node's witnessed domain. The formula C_g^{-1} t h is typed from Lg_Y^* Rf_!^d K to Rf_!^d Lg_X^* K; h^{-1} t^{-1} C_g has the opposite type and its products in both orders reduce to the identity. Functorial preservation of inverse gives exactly the requested final expression. This uses no claim of independence of the exchange from c.

I checked delivery-errors B-E against the actual node and cited statements: no new statement-only nodes to disguise a clause of the item; no unsupported transport comparison, no extra separation/properness assumption, and no node citation taken from a proof rather than its statement. citations.json contains exact statement substrings, checked against the current repository. All four steps are below 2000 characters. Small cases include the zero complex, the empty source, f = identity, j = identity for proper f, and d = c: the formulas remain well typed and inverse cancellation still applies. The argument is independent of boundedness and of separatedness of X_0 or Y_0 over k_0. Off-unit generic open-square and etale-comparison/coherence tools are declared in split_report.tool_uses with their specific purposes.
