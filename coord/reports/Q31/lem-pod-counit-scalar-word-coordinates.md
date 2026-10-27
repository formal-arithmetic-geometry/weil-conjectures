## Worker report

Item: lem-pod-counit-scalar-word-coordinates. Group: Q31. Stage 1, direct delivery.

### Files written

- dag/nodes/sec-poincare-duality/lem-pod-counit-scalar-word-coordinates.json: split; six proof steps using existing nodes. The statement and all original source/provenance fields are unchanged.
- citations.json: one verbatim statement quotation for each of the eleven step/node citations.
- report.md: this report. searches.jsonl is the unmodified log produced by msearch.py.

### New nodes

None. Zero new nodes and zero Mathlib leaves. The model-existence and substitution facts already have general DAG nodes, and the remaining unit/naturality manipulation is written out in the item rather than promoted to a node.

### Attachments

None. Searched lean/WeilConjectures for the exact blueprint id and for counit/scalar/word and realization/substitution terminology. There is no declaration stating this item. The related lean/Sheaf/Paper/IsomorphismScalarComparisonAgreement.lean theorem (lines 76-88) ends in sorry and does not establish this item.

### Literature

Read the current blueprint's sec-poincare-duality/sk-lem-finite/prop-weil-operations.proof.md, first sentence, and sec-six-functors/sk-rem-sf-pf-done/lem-fix-weil-operations.proof.md, first paragraph. The former delegates equivariant lifts to the latter, whose pullback/inverse-automorphism squares motivate this normalization. Neither text states the word-coordinate identity verbatim. The proof is correctly marked agent-written.

Read Stacks proetale.tex Tag 099N, lemma-pushforward-Noetherian-case, especially (2),(5) and their proof: completed inverse image is inverse image followed by derived completion and has the displayed quotient-limit formula. Read sites-cohomology.tex Tag 0941, lemma-derived-limit-is-ok, statement and proof: one K-injective whole-system representative computes the total limit and its cone comparison. These are supporting literature for the existing model/substitution nodes, not claims that Stacks itself states the additional scalar-word coherence.

WANTED: none. No SGA source is used.

### Searches and reuse

Read the live node and its existing searches, the chapter and unit records, the original source definitions, and the complete statements of every proof dependency. Searched the whole DAG for word coordinates, quotient-generator normalization, K-injective-counit normalization, and balanced reassociation. This located lem-trf-effective-comparison-realization-models, lem-trf-counit-realization-substitution and lem-pur-normalized-actual-reconstruction-maps. Also read lem-pur-normalized-reconstruction-adjunction-calculus, the whole-system operation definition, and lem-trf-quotient-system-mixed-coherence to check the meaning of their interfaces. The latter results are not unnecessary extra proof citations.

Ran blueprint_refs.py ancestor (prop-weil-operations), and whole-blueprint searches for 'counit scalar', 'realization', 'counit', and 'scalar pullback'. No blueprint node states this specified-coordinate equality. Its same_as remains empty and from.place retains its precise original extraction place.

Ran the required msearch.py leanfinder, loogle, leansearch and grep searches, followed by a second semantic phrasing about transporting comparisons across adjoint equivalences and a second grep for derived completion/quotient towers. All services answered. The hits are ordinary sheaf pullback adjunctions, Dold-Kan equivalences, general counit naturality and ordinary algebraic adic completion. Read SheafOfModules.pullbackPushforwardAdjunction and conjugateEquiv_pullbackComp_inv in Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean (lines 60 and 177); these are underived pullback/mate statements and provide no simultaneous completed quotient-system model or the prescribed normalized comparison. No hit states the item or specializes to it in one line. The item preserves inherited search records and appends exactly the searches logged for this work.

### Problems and completion

No statement correction or STATEMENT-DISPUTED finding. The main risk in the unsplit item was treating arbitrary finite reduction isomorphisms as if they identified the specified whole-system comparison. Steps 3-5 instead use the actual adjunction unit and counits, the general substitution formula, and naturality of the specified lambda/mu comparison. No change to a unit/chapter route is made. Nothing mathematical remains unfinished in this split; its existing dependencies remain independent items where not already finished.

## Not duplicates

No new nodes were created. The general model, reconstruction and substitution statements are reused, not reintroduced as specialized nodes. This item includes existence/domain assertions and fixes beta through b at K; the general substitution node supplies the r-word formula at a realized system. Step 3 explicitly relates these two coordinates by the actual completion unit.

## Review by Q31

I read sections B-E of coord/delivery-errors.md against the six written steps and the source statements. There are no new-node form or duplicate issues: no statement-only node, source tag, or proof sketch has been invented to carry one of this item's clauses. All step texts are below 2000 characters, with their elementary calculations visible. The statement's definitions and its source provenance were retained.

In Step 1 I checked the complete statement of lem-trf-effective-comparison-realization-models: it permits E contained in L contained in M with equality and supplies simultaneous models for every P, actual quotient transitions, balanced reassociation, and the zero shifted Roos coordinate. I instantiate M=L. The separate lem-pur-kflat-change-of-rings explicitly applies to an arbitrary map of ring sheaves and preserves both K-flatness and termwise flatness, so it justifies Q and the quotient complexes without asserting flatness of A_E,n to A_L,n. The two balanced maps identifying Q's quotients are inverse by tensor balancing and commute with projections; this calculation is in the step.

In Step 2 I checked lem-pur-normalized-actual-reconstruction-maps for normalization of R K, the actual counit e, and the actual unit u_K, with no finiteness or Tor hypothesis. The effective-model node explicitly gives normalization and constructible-complete realizations of one primitive operation applied to R H. It does not simply state that every iterated system is effective. I repaired that potential C4 gap by writing the two applications to H=L D and H=L J, then transporting along S_X(e_D) and U_g,L(e_J). The first applications show these H are in the required constructible-complete categories. Naturality of the counit gives its invertibility on the transported systems. Thus every intermediate object used later lies in the substitution theorem's domain.

In Step 3 the statement of lem-trf-counit-realization-substitution gives natural isomorphisms r and the word factorization r_vw,C. The statement of lem-coef-derived-system-evaluation-calculus supplies the actual triangle identity used to calculate r_O,C O(u_K)=b_O,K. I expanded this identity and substituted it into both beta definitions, so the proof does not confuse coordinates at K with coordinates at L R K.

In Step 4 I checked that the substitution theorem includes precisely the specified scalar/pullback comparison among the allowed t. Its formula gives conjugation by the r-word isomorphisms at L C, as an identity of entire derived systems. I then compared it with the complete construction in lem-trf-integral-pullback-comparison-realization: lambda uses scalar change of the actual counit and balanced tensor association into the common g-pullback L-quotient tower; mu uses target-word pullback of the corresponding counit; epsilon is normalized by the ordinary limit cone on a K-injective tower resolution. Therefore their specified ratio is the counit-built comparison in that theorem. This checks identification of the particular arrow rather than existence of some arrow. The trf node does not depend on this item: its proof dependencies are the effective-model, substitution and mixed-coherence nodes, plus rationalization, so there is no back-edge here.

Step 5 uses the stated naturality of lambda/mu (hence a) at u_K and the two explicit formulas from Step 3. The displayed three equalities are ordinary composition and substitution. I marked only this step elementary; all model, reconstruction and counit-substitution invocations remain non-elementary and cite their theorem nodes. Step 6 uses the explicit representative/resolution descent of the effective-model node and the whole-diagram/whiskering assertion of the substitution node. These preserve the tower homotopies; I did not infer equality from evaluated finite arrows.

I tested the formula when K=0 (all maps are the unique zero-object isomorphisms), g is the identity (the same unit/counit calculation), E=L including arbitrary associated choices of uniformizer (all primitive comparisons become the canonical multiplication/completion ones), and genuinely ramified E contained in L (the finite quotient maps may be nonflat, but Step 1 uses change of rings of a K-flat source, not underived exactness of scalar extension). Shifts and unbounded flat-term representatives do not alter any calculation: the domains concern their represented constructible-complete objects, and no bounded or finite-Tor resolution is assumed.

The six non-unit citations are generic tools already named by the item's definitions or needed to verify their domains. split_report.tool_uses explains each use for the maintainer; I did not set the maintainer-owned tool_uses field. No unit-level geometric route is replaced. There was no earlier sandbox split or returned-delivery entry to repair.
