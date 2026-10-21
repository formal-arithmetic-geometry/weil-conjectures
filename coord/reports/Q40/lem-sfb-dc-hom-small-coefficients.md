# Worker report: lem-sfb-dc-hom-small-coefficients

Group Q40; stage-1 repair, 2026-10-21. The dispatcher supplied the maintainer's return requiring a finer split of the 12006-character proof, while preserving the item's statement. The sandbox initially contained only dispatcher marker files: there was no node, report, citation file or search log to resume. I copied the current read-only repository node as the returned baseline, retained a baseline snapshot outside dag/nodes, and preserved its statement, original search records, Lean attachment and maintainer metadata. No repository file, launcher file or Lean file was changed, and no compiler or git command was run by the worker.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-dc-hom-small-coefficients.json: repaired item, statement unchanged; nine assembly steps, 2789 proof characters in total, longest step 457 characters.
- dag/nodes/sec-six-functors-basics/lem-sfb-internal-hom-localization-comparison.json: one new statement-only unsplit node. Its short proof sketch is preserved in this report. No Mathlib match. It proves the evaluation-defined comparison after inverting one scalar under sequential continuity, for arbitrary ringed sites. The preserved proof sketch is below 1800 characters in three steps. This is an operation comparison, not a finiteness-preservation clause of the item.
- citations.json: a verbatim statement quotation for every citation of every item step. Whole statements are copied where the application uses multiple clauses; no ellipses or adjusted hypotheses.
- support-citations.json: the corresponding quotations for the new node's proof steps.
- searches.jsonl: the actual command-generated search log. Existing item searches were retained; additional recorded searches include investigations that led to reuse of an existing embedding node rather than creation of another one.

## Attachments

None. The existing declaration AlgebraicGeometry.ProEtale.CondensedRing.isMonoidalClosed_boundedConstructible is still `sorry` at lean/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/BoundedConstructible.lean:485. The nearby tensor-closure instance proves a different operation. Neither constitutes a finished attachment of this item. The existing Lean and all maintainer fields remain as supplied by the repository.

## WANTED

No new document is needed. The existing norm-uniqueness node records that its textbook reference has not been obtained. This repair uses that node's stated theorem as an existing obligation, rather than claiming to have read or proved the unavailable textbook result.

## What changed and why

The returned proof repeated arguments already present in the DAG. The repair has one new non-elementary lemma; the remaining extracted arguments reuse existing nodes rather than duplicating them:

1. Former step 1 is now the short Noetherian/DVR setup and the two existing integral model/adic-criterion applications. General-lfp constructibility is still explicitly converted; it is never identified by definition with finite scalar local models.
2. Former step 2 is the existing normalized integral Hom reduction theorem, with its arbitrary-scheme hypotheses. Its derived-limit completeness clause remains unused.
3. Former step 3's slice-adjunction completeness argument is now the statement of lem-sf-ringed-rhom-derived-complete. Its vector-space flatness argument is now lem-exc-constant-field-module-flat. The residual assembly is constructible comparison, finite Tor amplitude, and the reverse adic criterion.
4. Former steps 4–5 are reduced to equality of the two point-pullback definitions and the existing finite-field-extension local-triviality theorem on each Noetherian stratum. Only E-coefficients need this bridge for continuity in the final argument; local triviality of algebraic-closure inputs is unnecessary once the objects descend.
5. Former step 6's scalar adjunction is used inside the new localization lemma. Its evaluation normalization and conservativity are now inputs to that lemma's short proof.
6. Former step 7 is the new localization lemma. The internal-sheaf continuity assumption remains explicit and is discharged using lem-sfb-constructible-internal-hom-continuity, rather than being inferred from global Hom continuity.
7. Former step 8 becomes essential surjectivity of the existing rationalization equivalence, the integral result, localization comparison and preservation of bounded constructibility under extension of scalars.
8. Former steps 9–10's finite-basis calculation, transition compatibility and filtered passage are already the precise statement of lem-sfb-dc-hom-filtered-colimit (its statement includes the evaluation-defined stage comparisons and transition compatibility). Those arguments are not repeated inline. The parent only verifies its finite-free, common-lower-bound, continuity and exactness hypotheses.

I also made the arbitrary finite normed extension/closed-unit-ball constructors explicit: finite dimensionality makes powers linearly dependent, an existing algebraic-embedding theorem chooses an embedding, and the existing unique-absolute-value theorem makes the original norm equal to its induced norm. Thus the ring and topology used by the embedded-coefficient lemmas agree with the actual constructors. This neither changes the statement nor adds a hypothesis.

The item source's obsolete external SGA citation was replaced with Bhatt–Scholze references. The proof follows the prescribed blueprint coefficient-passage route and uses no SGA theorem. The original statement and imported blueprint metadata are not modified.

## New node proof and source

The new localization node follows the formal scalar-localization argument behind Bhatt–Scholze Lemma 6.8.12 and Proposition 6.8.14(2), pp. 61–62, but is marked agent-written. I read those paragraphs and Remark 6.8.15 in the local PDF. The source's Lemma 6.8.12 is a global Hom/direct-sum assertion; the new statement does not misattribute its internal-sheaf continuity hypothesis to that lemma.

The full argument is preserved in this report: sheaf tensor preserves colimits, so tensor by R[1/s] is the exact repeated-scalar telescope. Apply the assumed continuity to a bounded-below representative of L. The resulting isomorphism is the restricted scalar-adjunction comparison because its stage-n evaluation is h(k)/s^n. Conservativity of restriction gives the result over the localized ring. Naturality follows from the evaluation normalization. All three proofs steps are individually below 700 characters. There is no perfection assumption and no implicit completion of the ambient category.

## Not duplicates

lem-sfb-internal-hom-localization-comparison vs lem-sfb-dc-hom-filtered-colimit: the existing theorem assumes a diagram of R-algebras with finite-free stages; scalar multiplication by s on R is a module map, not a unital algebra map, so its localization telescope is outside those hypotheses. The new theorem handles that module telescope.

lem-sfb-internal-hom-localization-comparison vs lem-sfb-dc-hom-scalar-adjunction: scalar adjunction identifies the target after restriction, but does not assert that Hom commutes with localization. The new theorem proves the missing continuity comparison.

lem-sfb-internal-hom-localization-comparison vs lem-sfb-constructible-internal-hom-continuity: the existing result concerns changing the second input over a fixed coefficient ring, with constructibility and Noetherian hypotheses. The new theorem assumes precisely its sequential-continuity conclusion and proves the evaluation-defined change-of-ring isomorphism.

lem-sfb-internal-hom-localization-comparison vs lem-sf-ringed-localization-rhom-orthogonality: the latter is a coextension/vanishing statement for Hom out of an already localized complex; it does not identify scalar extension of Hom.

lem-sfb-internal-hom-localization-comparison vs lem-pur-integral-operations-scalar-extension: the latter extends between integral rings of two finite extensions using derived-complete systems. It neither inverts a scalar nor works on arbitrary uncompleted ringed-site complexes.

Whole-DAG searches for localization/internal Hom and searches of the complete imported blueprint found no identical theorem. Blueprint search queries included 'internal Hom complete', 'localization internal', 'finite Tor field', 'constant local model', 'Hom localization', 'Hom reduction', 'derived complete', 'localization Hom', 'invert scalar', and 'scalar extension internal Hom'. Existing lem-sf-ringed-rhom-derived-complete and lem-exc-constant-field-module-flat were reused; neither was recreated. Searches for finite normed, isometric and algebraic embedding led to reuse of lem-weil-pbc-algebraic-extension-embeds-algebraically-closed. The new node's blueprint origin is the existing explicit lem-sfb-dc-hom-preserves origin of the item, via the item; the mechanical ancestor lookup follows created.item into a former stage-3 module name and prints None, the first preflight required the mechanically computed null ancestor. I therefore set from.node to null, retaining the exact mathematical blueprint place in from.place and the item in via. The parent's already recorded blueprint origin is unchanged.

## Review by Q40

I read the chapter and restricted-functor unit, the current blueprint Hom statement, the returned item's complete proof, and all cited node statements. I read the local Bhatt–Scholze PDF at Lemma 3.4.11, Definition 6.5.1, Lemma 6.7.13, Proposition 6.8.11, Lemma 6.8.12, Proposition 6.8.14 and Remark 6.8.15. I also read Stacks fields.tex lemma-map-into-algebraic-closure (09GU), algebraization.tex lemma-derived-complete-internal-hom (099A), proetale.tex section-constructible (09AI) and section-suitable-derived (09C0), and the flatness definition/local criterion in sites-modules.tex (03ER/08FC). I checked the actual Lean finiteness-coefficient constructors and the still-sorried Hom instance. The imported statement, as requested, is unchanged.

For step 1 I checked that the embedding statement permits any algebraic extension and that the absolute-value statement gives uniqueness on this very finite extension. Dependence of 1,x,...,x^d proves algebraicity directly; injectivity of a field map and equality of closed unit balls are elementary. Postcomposition with the resulting topological ring isomorphisms is exactly the condensed-ring definition.

For step 2 the finite-type theorem states the Noetherian conclusion used here. The DVR theorem supplies both uniformizers and finiteness of the residue field, while ell has norm less than one and therefore maps to zero in that field. The coefficient-colimit statement gives the precise inverse limit used by the adic criterion.

For step 3 I checked both directions and the torsion allowance of the integral model comparison. The criterion's condition (1) explicitly uses those finite scalar models, and condition (2) explicitly supplies local completeness and an etale-origin bounded constructible finite-Tor reduction. Thus no hypothesis on the matrices in the original general-lfp presentations is silently imposed.

For step 4 I checked that integral reduction comparison allows arbitrary schemes and ambient complexes, with no geometric finite-field assumption. The finite-field finiteness child allows arbitrary positive-characteristic ground fields, which is needed here. The complete-Hom node uses exactly the local slice-localization definition of completeness used by the criterion, unlike the separate derived-limit clause of the reduction lemma.

For step 5 the constructible comparison requires qcqs X and a discrete Noetherian coefficient ring; Noetherian X and the finite field A satisfy both. The constant-field flatness node concerns arbitrary module sheaves, not just constructible ones. Tensoring with such a sheaf is exact, so applying it degreewise preserves cohomology bounds and proves the stated Tor interval. With this etale witness and local completeness, condition (2) of the adic criterion applies, and the integral-model comparison returns exactly general-lfp constructibility.

For step 6 I checked the continuity node requires finite scalar local models of K0 and a common termwise lower bound, not a site-perfect K0. The integral comparison supplies those models. A bounded-below representative of L0 provides the repeated-ell diagram with its common bound. The Grothendieck module-category statement supplies exact filtered colimits, and the coefficient-colimit statement identifies precisely the module localization used by the new node. The new lemma's own proof quotes tensor-colimit preservation, the explicit telescope definition, exact functor passage to derived categories, and the scalar-adjunction/conservativity statement. I checked the evaluation formula on every telescope stage, which is necessary to identify the canonical map.

For step 7 I checked that the rationalization equivalence is compatible with scalar extension and that the localization has the same objects as the integral category. Its integral representatives meet the general-lfp condition used in step 3. The extension-preservation statement is for this very O_E-to-E map. The rational conclusion follows from the existing integral result and comparison without invoking itself.

For step 8 I compared the two point-pullback definitions: both are sheafified Kan extension from profinite sets followed by structure pullback. The finite extension coefficient sheaves therefore agree. The local-triviality statement applies separately on every Noetherian locally closed stratum and gives finite free E^r models, sufficient for the scalar-model continuity theorem. A new equivalence-of-constructibility lemma here would only duplicate this direct application.

For step 9 I checked that the two-colimit statement descends whole derived objects, not only their cohomology. Two fields of definition are enlarged to their compositum by the existing extension-preservation statement. The finite-free coefficient theorem provides the actual module bases required by the filtered comparison. Fields containing E are a small filtered cofinal subposet, since any finite field is included in its compositum with E. The whole statement of filtered-Hom comparison supplies transition compatibility; no part of its proof is being used as an unstated extra conclusion. The bounded-below input is L_E, not an unbounded injective replacement. Step 8 supplies the exact continuity hypothesis, and the final extension-preservation lemma carries the already bounded constructible H_E to the source of the comparison.

I tested the new localization statement for s=1, s=0, an already invertible s, K=0, L=0, and a one-object ringed site. It reduces respectively to the identity, zero coefficient category, identity scalar extension, or the usual localized module-Hom comparison under continuity. I deliberately retained the continuity and lower-bound hypotheses: removing them would allow infinite-product Hom counterexamples. For the assembly I checked empty X, zero complexes, E=Q_ell, and torsion integral cohomology; none requires a nonzero rank, torsion-freeness, or a nonempty stratum. No new node is a clause of the finiteness assertion, no elementary coefficient-predicate application became a node, and no proof step is over 2000 characters. Every cited conclusion is a verbatim part of a statement recorded in citations.json or support-citations.json.

## Validation and unfinished work

The remote review_split check passed on the assembly. A read-only traversal found an existing downstream cycle involving lem-pc-ring-hom-extension-differential and its adjacent-degree child; that edge is outside this delivery. A separate reachability check verifies that none of the dependencies returns to either changed or new node, so this repair introduces no cycle. The server check remains authoritative. The main statement is byte-for-byte equal to the baseline. The complete new lemma is included in its node as explicitly requested by the human's re-split instruction. Both required dry-run attempts have now exited. Final results and the tool incompatibility are recorded below; no delivery was pushed.

First deliver.py --no-push exited 1: it rejected the new node status split and its explicit mathematical blueprint ancestor. The ancestry field was corrected to the exact null ancestor that blueprint_refs.py computes from the maintainer-owned created.item chain. The complete child proof remains in its node to satisfy the human's explicit re-split requirement. No push was attempted.

## Final tool blocker

After correcting ancestry, the second deliver.py --no-push exited 1 with exactly one refusal:

> new node lem-sfb-internal-hom-localization-comparison: status 'split'; a new node is unsplit or mathlib

The remote split review passed; the delivery's search and citation checks and its other preflight conditions passed. The human return explicitly requires extracted nodes to have statements, sources and short proofs in words. The new child contains that complete 1649-character proof, and the unchanged-statement parent is now a 2789-character assembly. The stage-1 preflight still permits only statement-only unsplit children or Mathlib leaves. Marking this non-Mathlib child as unsplit while retaining the proof also violates the preflight, and discarding its proof would undo the explicit repair requirement. The worker cannot edit the preflight, launcher, maintainer-owned provenance, or another existing node to bypass this condition. The complete repair is retained in the sandbox for the maintainer; a preflight exception for this human-authorized finer split is required before it can be pushed. No push command was run. Final outcome: BLOCKED by this format restriction, not by mathematics or compilation.

## Retry verification, 2026-10-21

Resumed the retained repair without rewriting its mathematics or searches. Compared the sandbox item with both baseline-item.json and the current read-only repository node: the current repository still equals that returned baseline and the sandbox statement remains unchanged. The parent retains its 2789-character assembly, and the child retains its 1649-character proof.

Ran the required initial retry of `python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q40 lem-sfb-dc-hom-small-coefficients --no-push` and polled that same process to completion. It exited 1 with exactly the same sole refusal: `new node lem-sfb-internal-hom-localization-comparison: status 'split'; a new node is unsplit or mathlib`. Route notices were explicitly recorded as non-refusals. Nothing was pushed, and no second invocation was active.

The human return requires the extracted child to carry its source and short proof in words; the preflight still disallows its split status. The repair is retained intact. No tool was edited or bypassed, no proof was discarded to satisfy the gate, and no artificial Mathlib match was claimed. This retry is BLOCKED by the unchanged delivery-format restriction.


## Resumed repair under the final route note, 2026-10-21

The dispatcher now explicitly requires NEW statement-only children (status unsplit, no proof steps), superseding the earlier wording interpreted in the historical blocker sections above. This resolves that format blocker without a tool exception. The existing localization child is retained with its identical self-contained statement, source, blueprint origin and actual logged Mathlib searches; only its proof fields and split status are reset for the next stage-1 worker. Its complete previous proof is preserved below as report material, as required by delivery-errors B1. The parent statement and its nine-step, 2789-character assembly remain unchanged. This is a substantive repair of the child format, not an unchanged re-push.

### Preserved localization proof sketch (report only)

1. Write $H_R=R\mathcal Hom_R$. By the telescope description of localization and preservation of sheaf tensor colimits, $S\otimes_R M=\varinjlim(M\xrightarrow{s}M\to\cdots)$ for every module sheaf $M$. Exactness of filtered colimits makes this functor exact: apply the telescope to any short exact sequence. Thus scalar extension is computed termwise on all complexes, and its derived functor agrees with ordinary tensor.

   Cites: def-weil-pbc-ringed-site-section-localization, lem-weil-pbc-independent-sheaf-tensor-colimits, sk-def-sfb-derived-categories

2. Choose a representative $L^\bullet$ vanishing below one integer. Its repeated-$s$ diagram has that common lower bound. The assumed continuity, applied to this diagram, and the tensor-colimit identification of step 1 give an isomorphism $S\otimes_R^{\mathbf L}H_R(K,L)\simeq H_R(K,S\otimes_R^{\mathbf L}L)$ in $D(R)$. The transition on the left is multiplication by $s$: both scalar actions transpose to $s$ times evaluation. Its stage-$n$ map to the target is $H_R(K,L)\to H_R(K,S\otimes_R L)$ followed by multiplication by $s^{-n}$. These stage maps are compatible because the unit $L\to S\otimes_R L$ is $R$-linear.

   Cites: def-weil-pbc-category-colimit, def-pur-derived-internal-hom, lem-sf-ringed-derived-closed-symmetric-monoidal

3. The scalar-adjunction isomorphism identifies $H_R(K,S\otimes_R^{\mathbf L}L)$ with the restriction of $H_S(S\otimes_R^{\mathbf L}K,S\otimes_R^{\mathbf L}L)$. Under this identification the restricted evaluation-transpose comparison is the map of step 2: at stage $n$ its pairing sends $(k,h/s^n)$ to $h(k)/s^n$. Equality on these telescope stages gives equality of the induced map, rather than only an abstract isomorphism. The conservativity clause of scalar adjunction now shows that the comparison is an isomorphism in $D(S)$. Naturality follows from the same evaluation identities and functoriality of colimits.

   Cites: lem-sfb-dc-hom-scalar-adjunction

The retained support-citations.json documents those historical proof-sketch citations; the new child has no proof dependencies. citations.json remains the authoritative quotations for the parent assembly. The old final-tool-blocker/retry sections record previous attempts, not the current delivery outcome.


### Current resumption review (signature: Q40)

I re-read delivery-errors B–E in full, the current chapter/unit, the blueprint Hom statement and Bhatt–Scholze §§6.8.11–6.8.15 in the retained PDF text. I compared the returned baseline with the current read-only repository: they coincide, so no mathematical rebase is needed. The live Hom instance still ends in sorry, and does not justify ATTACH. I re-read every statement cited by all nine parent steps and every statement dependency of the child. The step-by-step hypothesis checks in Review by Q40 above remain valid: in particular the reduction theorem states its canonical map for arbitrary complexes; the separate completeness theorem uses local slice completeness; continuity explicitly requires finite scalar local models and a common lower bound; and the filtered-Hom theorem supplies the actual evaluation-defined comparison and compatibility. These are statements, not arguments borrowed from their proofs.

I read the actual retained searches.jsonl results, including both LeanFinder phrasings, both Loogle patterns, LeanSearch and both grep patterns for the localization child. The hits concern underived closed structures, category localization, generic derived-functor maps or Ext-smallness, rather than the conditional coefficient-localization comparison. No query or result was invented, and no unchanged search was repeated. I rechecked the whole-DAG localization/Hom candidates and the blueprint search: the telescope-dual theorem has the free telescope in the first Hom argument and produces a product; the bounded-localization-complex calculus concerns slice restriction/currying. Neither states the new scalar-extension comparison. The existing finite-free algebra-colimit comparison excludes the repeated-scalar module telescope, since multiplication by ell is not a unital algebra map.

For the child, the site universe, exact filtered colimits, bounded-below L and explicit continuity of K are all retained. For s=0 its telescope and localized ring are zero, for s=1 or an already invertible s the comparison is identity scalar extension, and zero K or L gives zero. The one-object case is the usual conditional localized module-Hom formula. The parent still handles empty X, zero complexes, torsion integral cohomology and E=Q_ell without extra assumptions. All nine steps are at most 457 characters; no non-elementary argument longer than 2000 characters remains. The new node is a general operation-comparison lemma, not one of the coefficient-finiteness clauses of the parent. It now correctly awaits its own future split.

The only current correction is the explicitly requested child format. Its proof and citations are retained in this report/support-citations for continuity, while proof=[], proof_deps=[], proof_origin=null and status=unsplit satisfy the final route note. I verified all 34 parent step/node quotation entries against the current statements and retained citations.json unchanged.


## Current validation outcome

The resumed final dry run exited 0: `OK (not pushed) deliver/Q40/lem-sfb-dc-hom-small-coefficients at 7bc8d9a06ea: preflight passed`. The earlier format blocker is resolved by the final route note. No delivery command overlapped another. The push follows this successful dry run; no mathematics or node fields were changed after it.
