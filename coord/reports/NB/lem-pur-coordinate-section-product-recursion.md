## Worker report

Item: lem-pur-coordinate-section-product-recursion. Group NB. Stage 1 only, direct delivery, 2026-10-22.

### Files written

- dag/nodes/sec-smooth-purity/lem-pur-coordinate-section-product-recursion.json: split into ten proof steps; statement and statement dependencies preserved.
- citations.json: 37 step/node entries quoting the exact current dependency statements.
- report.md: this report. searches.jsonl was written by the prescribed search command.

### New nodes

None: zero new nodes and zero new Mathlib leaves. The coefficient comparison, projection formula, product laws and adjunction definitions already exist. The identification of coefficient multiplication with the projection map is a short calculation inside the item's proof, not a new lemma.

### Attachments

None. I searched lean/WeilConjectures for the exact item tag and for coordinate products, supported cups and recursion. There is no item declaration. The nearby isIso_supportedClassMap_kummerBoundaryProduct_coord in EtaleCohomology/Purity/Smooth/ThomClass.lean:47 ends with sorry at line 52 and asserts isomorphy, not the complete recursion and arbitrary-mate identities. It does not finish this item. SupportedCup.lean supplies related definitions, not all clauses of this statement.

### WANTED

None. The item's main-20261015 proof is present. The additional tensor/projection and mate calculations below are supplied explicitly by the worker and marked proof_origin.by = agent.

### What changed and why

The item had no proof steps. I retained its statement, source, creation metadata, blueprint ancestry and previous searches, and supplied an actual map calculation. In particular I did not infer the desired equality merely from isomorphic source and target objects or from rank-one purity. I did not use a relative supported Kunneth assertion. There is no statement dispute or source correction. The existing arbitrary-pullback product node and the Cartier node cover arbitrary base change once each coordinate divisor remains Cartier, which the polynomial calculation verifies even over nonreduced bases.

The original definitions use A_{E,n+1} with n in N, while this item uses A_{E,n} with n >= 1; reindexing by n-1 covers precisely the same coefficients. No bound related to ramification is added.

### Searches

Whole-DAG keyword searches and tools/blueprint_refs.py searches for coordinate, supported cup, and projection-formula found the existing interfaces used here, not another node stating this complete auxiliary recursion. The blueprint ancestor command gives cor-pur-affine-space-zero-section-purity. No new node was created. I preserved the existing Mathlib search entries and added the five searches actually run with batch2/msearch.py (two LeanFinder phrasings, Loogle, grep in AlgebraicGeometry, LeanSearch); their actual summaries are in searches.jsonl and the node. LeanFinder returned projective-spectrum and general sheaf adjunction declarations; LeanSearch returned Kahler differential/base-change declarations. Neither states this item. Loogle returned CategoryTheory.Adjunction.comp_homEquiv, read at Mathlib/CategoryTheory/Adjunction/Basic.lean:584 (with comp and its unit/counit formulas at lines 567–582). It gives only the formal composite Hom bijection, already represented by the existing composite-adjunction node; it is not a match for supported Kummer products and exceptional base change. The prescribed Mathlib grep returned no hits.

### Unfinished work

No part of the one-level split is left open. Existing cited nodes remain their own separate items; no Lean was written or compiled.

## Not duplicates

No new nodes, so there are no new/existing node pairs to distinguish. In particular I reused lem-pur-supported-cup-functoriality, lem-pur-etale-closed-constant-tensor and the finite compact projection node instead of creating coordinate-specialized copies. The parent cor-pur-affine-space-zero-section-purity is not cited: doing so would be circular.

## Review by NB

I read the item, the chapter and sk-prop-an unit, the three-level route rule in SETUP.md, GOAL.md, stages/1-dag.md, coord/brief-stage1.md, and delivery-errors B–E. The source read for the item is literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/cor-pur-affine-space-zero-section-purity.proof.md, specifically its iterated-affine-line ordered-product sentence and its final Cartier/base-change paragraph. The split realizes those sentences on actual maps. There are no new nodes needing a separate source audit. All dependency statements used were opened in dag/nodes; I did not take an unadvertised lemma from a dependency's proof.

1. Step 1 uses the coordinate-boundary definition to fix the ordered coordinates and the Cartier-map statement to know exactly when pullback is permitted. The polynomial nonzerodivisor calculation verifies that hypothesis. The finite-twist local-freeness statement supplies rank-one finite constructibility, and the finite compact projection statement applies to the closed zero section with its pulled-back shifted Tate line. The base schemes and affine towers remain separated finite type; the coefficient ring is the given finite A, not a field or a ramification-restricted quotient.

2. Step 2 uses the actual tensor-morphism cup definition, its pullback law in lem-pur-supported-cup-functoriality, and Cartier naturality to identify the first r factors with q^*C_r. The Thom-map and class-operation definitions specify the total-intersection source transport and twist multiplication. These statements do supply an equality of morphisms, not only of their cohomology groups. The intersection has the full coordinate ideal, so it is the stated B, not just a set-theoretic support.

3. Step 3 uses the counit formula of def-kun-projection-formula-map and the ordinary etale closed-constant tensor lemma. The latter explicitly states flatness, the restriction/multiplication map and its derived normalization. The cup definition is exactly multiplication of the same restricted sections. Thus both coefficient arrows send a tensor to the same product. This is an elementary normalization calculation from the cited constructions. It does not claim the finite projection theorem on an input outside its hypotheses: invertibility at N comes from the supported coefficient isomorphism.

4. Step 4 uses naturality of the counit construction and the finite compact projection isomorphism at W_r. The displayed naturality square is obtained by substituting C_r into that construction; it is the step that converts the tensor product into s_*C_r followed by the orientation. The supported cup symmetry statement and normalized class operations account for ordering and the sign 2 times 2r. This is not a new node restating the recursion: the calculation carrying the recursion is written here.

5. Step 5 applies the explicit empty-product clause of the Thom-map definition and the identity-adjunction clause of def-weil-pbc-composite-adjunction. This checks both rank-zero assertions, including their normalization.

6. Step 6 opens the composite-adjunction definition: its stated counit and its composite Hom bijection are exactly what the calculation uses. The exceptional-inverse-image and Thom-map definitions identify the two arrows with their adjuncts. The conjugate-adjunction definition supplies the specified comparison d_r. Counit naturality is expanded in the displayed formula. No right-adjoint tensor formula or purity theorem is smuggled into the elementary transpose calculation.

7. Step 7 uses Cartier naturality on each divisor and the product pullback law. The ordinary closed-constant lemma explicitly states compatibility of its exchange with coefficient restriction and composition, so the source identification is the normalized one in the statement. The polynomial check from Step 1 applies to B' as well; no flatness or smoothness of g is needed.

8. Step 8 uses the defining transpose of the mate in def-weil-pbc-adjunction-mate, together with the exceptional Hom bijection and the definition of theta. I checked the direction: e is the inverse closed-direct-image exchange, from z'_*g^* to g_c^*z_*, and its mate goes from g^*Rz^! to Rz'^!g_c^*. The displayed counit/naturality calculation gives C'_c by Step 7. It proves the required equality without assuming that this mate is an isomorphism.

9. Step 9 uses exactly the site-comparison clause of supported cup functoriality, the etale-witness clause of the Cartier node, the realized-transformation clause of the finite compact projection node, and the natural etale-origin Hom bijections in thm-sf-ambient-adjoint-class. The exceptional-inverse-image definition explicitly specifies their transport via compact support and full faithfulness. All sources are bounded below of etale origin. A twist shifted by 2r is still bounded below for each fixed r; a uniform lower bound for every r simultaneously is not required. This avoids an ambient unbounded pro-etale adjunction assumption.

10. Step 10 uses the Cartier node's explicit exponent-independence assertion and the cup node's graded commutativity with canonical support symmetry. The degree of each boundary is 2. The normalized signed-twist multiplication is supplied by the class-operation definition. Changing an exponent or swapping coordinates therefore changes no map before or after transposition.

For delivery-errors B, there are no unsplit new statements, new notions, or new sources needing a Stacks tag; no new node can be hollow or have a missing definition. Existing sources, blueprint fields and search records are preserved. For C1/C4 I matched every use above to the opened statement, and citations.json uses verbatim excerpts. No definition is cited as if it asserted product functoriality: that comes from lem-pur-supported-cup-functoriality. The generic off-unit projection, coefficient and adjunction-comparison tools are declared in split_report.tool_uses for maintainer review; no top-level tool_uses was written. For D the proof's tensor square and counit calculation carry the argument in the item, with no new clause-copy nodes and no citation of the parent. For E I checked r=0, r=1, empty B, nonreduced B (a polynomial variable is still injective), arbitrary nonflat g, arbitrary positive coefficient index and ell=2 (all relevant signs are +1). The argument never replaces a scheme-theoretic intersection by its underlying set. Each proof step is under 2000 characters; none hides a long lemma or unnamed comparison.

I corrected no inherited statement; the substantive refinement made during self-review was to distinguish the coefficient projection map pi_N, whose inverse comes directly from multiplication of supported units, from the finite-Tor projection isomorphism pi_Wr. I also explicitly cited the exceptional-inverse-image definition in the site-transport step, so its normalization is supported by the statement rather than inferred from an abstract existence of adjunctions.
