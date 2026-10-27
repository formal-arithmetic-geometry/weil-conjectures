# Worker report: lem-sf-semilinear-slice-scalar-generators

## Files written

- dag/nodes/sec-six-functors/lem-sf-semilinear-slice-scalar-generators.json: statement, split; eight proof steps; no Mathlib match for the full statement.
- citations.json: a verbatim statement excerpt for every step/node citation.
- report.md: this report and self-review.
- searches.jsonl: six genuine Q67 search calls, retained by the search command; no unavailable service in these calls. The item's five inherited search entries are retained unchanged.

There are zero new nodes and zero new Mathlib leaves. The scratch helper write_split.py is confined to this sandbox and is not a DAG delivery file.

## Attachments

None. The exact blueprint-tag search over lean/WeilConjectures found no declaration for this item. Searches for semilinear systems and extension/tensor comparisons found no declaration giving the full arbitrary-site, arbitrary-algebra-tower statement. ExtensionByZeroPresheaf.lean constructs the direct-sum presheaf; it does not assert this tensor/tower comparison. OpenRestrictedOrdinaryComparisonSquare.lean and CoefficientTargetGeneratorScalar.lean concern different geometric/stalk comparisons and do not assert this item.

## WANTED

None. The sources used are present in literature/.

## Corrections and scope

The item was an unsplit statement with an empty proof and no recorded Lean audit. I kept its statement and statement dependencies unchanged. In particular I retained arbitrary sheaves of commutative coefficient algebras and unital, possibly non-surjective transition maps. The proof now distinguishes the ordinary O-linear projection comparison from its B_n-linear realization and constructs the underlying scalar identification directly from the defining direct sums.

The blueprint ancestor is fix-prop-coherence. I read its available main-20261015 proof in sk-thm-sf-package and the current unit record sk-thm-sf-compatibility, together with the chapter record. This item realizes the sentence about tensor reassociation, evaluation, and adjunction units/counits in the coefficient-coherence part; it is not the unit's key statement, so no unit record is changed. Searches of the whole blueprint for semilinear, scalar, strict semilinear, localized ringed, 0E8I, and restriction of scalars found no duplicate blueprint statement. The existing ringed-slice tensor-generators node provides the ordinary normalized comparison and is used rather than recreated. The existing scalar-restriction coherence node is limited to finite constant coefficient rings on scheme pro-etale sites, so it cannot replace the arbitrary-ringed-site argument here. No unit route is replaced.

Mathlib searches used only msearch.py, including both natural-language phrasings, Loogle and source grep. The hits were read. SheafOfModules.restrictScalars (Sheaf/ChangeOfRings.lean:37) supplies the restriction functor only; PresheafOfModules.sheafificationAdjunction (Presheaf/Sheafification.lean:125) supplies module sheafification only; ModuleCat.ExtendRestrictScalarsAdj.unit and its coherence hits concern modules over rings, without localized-site extension by zero. The second semantic phrasing returned module localizations and Tilde maps. None states the item or specializes to it in one line. No fresh search result is invented, and no old query is represented as a new Q67 call.

## Unfinished work

None within this stage-1 item. The ordinary comparison remains its existing DAG node, as required for a one-level split; this delivery does not split that other item.

## Review by Q67

I read Stacks sites-modules.tex at Tag 0E8I (lemma-j-shriek-and-tensor), Tag 03DI (lemma-extension-by-zero), Tag 03CY (lemma-sheafification-presheaf-modules), and Section 03EK, including Tag 0GMW and the bilinear universal-property display. I also read sites.tex at Tag 00WK (lemma-sections-sheafification) and its section-sheaves-algebraic-structures, especially the commuting forgetful/sheafification diagram. The proof origin is agent: the coefficient and generator equations are an explicit refinement of the existing ordinary comparison, not a claim that Stacks states all the tower equations. No SGA source is used. No new node needs a separate source.

For step 1 I opened def-weil-extension-by-zero-presheaf, def-weil-presheaf-modules-sheafification, def-pc-sheaf-restrict-scalars, and lem-pur-site-restriction-module-adjunction-exact. Their statements actually give the direct sum, its summandwise action and restrictions, the same underlying abelian sheaf under scalar restriction, and extension as P_F#. Thus I can identify the underlying O-extensions and the B_m-restricted transitions by the identity on every summand. I checked the actions through O -> B_n and through B_m -> B_n separately. Neither exactness nor a coextension adjunction is inferred from a mere definition.

For step 2 I opened lem-pc-sites-sheafification-underlying-sets and lem-weil-pbc-site-sheafification-sections-local. The first explicitly identifies underlying set sheafification for abelian presheaves, so the second's local lifting theorem for sets applies to module sheafification. The extension-presheaf definition then makes each lifted section a finite sum, and the actual tensor definition makes each lifted tensor section a finite sum of pure tensors. Successive refinements suffice for the finitely many terms. This repairs the potential gap between a generator calculation and equality of sheaf morphisms: there is no global-generation assumption. The general local-section lemma is declared as a tool use, since no node of this unit states it. The underlying-set lemma is already a Mathlib leaf. I did not create another local-generation or sheafification lemma.

For step 3 I read the full statement of lem-sf-ringed-slice-tensor-generators: it explicitly asserts the isomorphism, the specified generator formula, its inverse generator formula, and naturality for arbitrary module sheaves on the localized ringed site. It is stronger than an unnormalized projection isomorphism. Each B_n is an O-module by the restriction-of-scalars definition, and the coefficient algebra's restriction is exactly B_{n,V}. Step 1 changes only the target's coefficient presentation. This step takes the existing statement, not an undocumented construction from its proof.

Steps 4 and 5 use the same tensor, extension-presheaf and scalar-restriction definitions, which I reopened. In step 4 the coefficient scalar c acts on the second tensor factor; its restriction multiplies b| in the same summand. The displayed equality proves linearity and the generator test extends it to all sections, including an extra scalar variable. Injectivity of the already constructed isomorphism proves inverse linearity. In step 5 I checked the target is restricted to B_m before comparing morphisms: q preserves the O-algebra action and commutes with restriction, so both displayed terms belong to the same n-th extension summand. The inverse-system square is obtained by actual cancellation of the two component isomorphisms, not by a new existence assertion.

Step 6 is a calculation with the presheaf definition's stated action on a morphism and the tensor definition's action in the first factor. Step 7 uses the sheafification uniqueness clause to compare the two maps from j_!G after evaluating each summand; the maps insert exactly 1, and unitality of q and of restriction is precisely the needed hypothesis. The two paths and their common value are written explicitly. In step 8 I checked def-pc-cochain-complex-modules states the chain-map equation used. Substituting d^i into step 6 proves that equation and substituting a chain-map component proves naturality; inverse compatibility follows by cancellation. There is only one degree at a time, so there is no hidden boundedness or totalization argument.

I checked the B--E return cases against the files: the proof does not move any clause into a new node, does not silently cite a definition for a theorem, and has no new statements needing notions, duplicate checks or Mathlib declarations. Every cited node's statement was opened, and every citation quote is a literal substring of that statement. All proof steps are under 2000 characters. The only non-elementary inputs beyond the already stated ordinary comparison are the two existing sheafification statements in step 2. The other steps spell out direct-sum, tensor, ring-map and inverse-cancellation calculations.

I tested the statement on a one-object terminal site (the comparison is the ordinary tensor identity), G=0, B_n=0, identity transitions, a non-flat quotient coefficient, a non-surjective map of coefficient algebras, and objects with no map to V (their extension presheaf is the zero direct sum). I also checked a site with several arrows W -> V: the formulas retain the arrow f and never identify different summands. Sheafification can still add sections locally, which is why step 2 is necessary. None of these cases needs flatness, surjectivity, completeness, a subterminal V, enough points, or a bounded complex. There is no statement dispute or source error.
