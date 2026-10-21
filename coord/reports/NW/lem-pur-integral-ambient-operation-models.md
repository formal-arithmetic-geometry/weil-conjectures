# Stage-1 report: lem-pur-integral-ambient-operation-models

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-integral-ambient-operation-models.json: statement split, with ten proof steps; no Mathlib match for the whole item.
- citations.json: a verbatim statement quotation for every step/node citation.
- report.md: this report.

No new nodes or Mathlib leaves. The sandbox was empty of node files on arrival; there was no previous split to overwrite. All original item fields, statement, blueprint provenance and historical searches were retained. The additional searches are the actual five calls recorded in this item's searches.jsonl. The local write_split.py is a sandbox-only generation helper, not a project or launcher change.

## Attachments

None. I searched lean/WeilConjectures for the blueprint id and the ambient/completed pullback and tensor notions. CompletedExchange.lean concerns a different constant/adically completed pullback construction; it does not assert both comparisons, their strict towers and normalized augmentations. No finished declaration states this item.

## WANTED

None.

## Corrections and scope

The statement is unchanged. Its explicit structural map is essential: this proof never assumes that inverse image commutes with the inverse limit defining the coefficient sheaf. It also never identifies a morphism between abstract derived-limit triangles with the specified functorial cone map. The original item had no proof; the draft provides the degreewise maps, their quotient-transition equations, their zero-component augmentation normalization and their descent to derived categories. No new lemma restates either clause. The existing integral tensor-reduction tower comparison is reused.

The chapter and sk-thm-sf-compatibility unit were read. This is the coefficient-operation construction below the final paragraph of def-weil-derived-pullback-tensor-hom, not a replacement geometric purity route. Its blueprint ancestor and via chain remain those recorded by the existing item; the whole-blueprint searches for ambient completion, quotient tower, completed tensor, scalar association and completion presentations found no other blueprint node stating this item exactly. There are no realized fields to fill for this non-key node. Generic ringed-site, K-flat, localization and Roos tools from other units are declared in split_report.tool_uses.

## Not duplicates

No new node was created. In particular lem-pur-kflat-total-tensor-model, lem-pur-integral-tensor-reduction-tower-comparison, def-pur-cochain-coefficient-arrows and lem-weil-strict-roos-derivation already supply the needed intermediate facts. These are reused rather than recreated.

## Sources and searches

I read sites-cohomology.tex at lemma-pullback-K-flat (0G7E), lemma-derived-base-change (06YY), lemma-pullback-tensor-product (07A4), and section-derived-limits / lemma-derived-limit-is-ok (0940/0941), including the proof's K-injective tower resolution and ordinary-limit inclusion. I read sites-modules.tex section-tensor-product (03EK), its scalar-extension identity, the bilinear universal property, lemma-sheafification-tensor and lemma-tensor-product-pullback (03EL). These are the generic tensor and representative arguments used here. The blueprint source read was main-20261015/blueprint/sec-proetale-coefficients/sk-def-sf-operations/def-weil-derived-pullback-tensor-hom.md. I also read Bhatt--Scholze pp. 16–18, 22–23 and 49–50: Proposition 3.1.9 supports exact products, Definition 3.4.10 explains completed tensor, and Lemma 6.5.9(4) explains the motivation for completed pullback. I do not invoke 6.5.9 to get this item's conclusion: it assumes qcqs schemes and is about complete objects, while the present statement is a comparison of explicit quotient-tower constructions on all ambient objects. No SGA route is used.

The first LeanFinder phrasing returned ordinary sheaf pullback and ordinary AdicCompletion facts. The second, about pullback/reduction and change of rings, returned SheafOfModules.pullbackComp and related ordinary pullback comparisons. I read PullbackContinuous.lean:106, 118 and 167: these concern ordinary sheaf pullback/sheafification and composition and do not give the asserted derived tower/augmentation comparison. Loogle's query "pullback", "completion" returned no hits; the logged Mathlib CategoryTheory grep for derivedCompletion|completedTensor|completedPullback returned no hits. LeanSearch returned AdicCompletion, profinite limit facts and ordinary sheaf pullback. These are not one-line specializations of the whole item. No service failure was misreported as absence.

## Review by NW

I checked this split against B–E with the cited node statements open. There are no new statements to check for B's self-containment or duplicate-tag issues; the item retains its complete hypotheses and all eleven original statement dependencies. Every quotation in citations.json is copied from a cited statement, and each step's uses occur in proof_deps. I checked that no cited node's proof is being used as though its stronger content were in its statement.

Step 1 uses the coefficient-sheaf limit definition and the actual constant-section inverse-image maps, not an inverse-image/limit comparison. Naturality for the quotient map follows from agreement on constants. It constructs the structural map by the limit property on X, which is valid for every f in the item. Step 2 uses exactly the flat-term K-flat resolution, ringed derived-pullback computation, preservation of flat-term K-flat complexes, K-flat total tensor and derived change-of-rings statements. All are unbounded statements and require no flatness of the structural ring map. In particular f*P is a valid simultaneous representative for all its quotient reductions.

In Step 3 I checked def-pur-cochain-coefficient-arrows really provides a natural scalar-association isomorphism for a compatible coefficient square. Its normalization is the map used here. The inverse and both scalar actions are written, and the required square was proved in Step 1. Step 4 uses the existing statement about entire tensor-reduction towers, then checks the normalization by the sheaf-tensor bilinear universal property. The tensor-colimit lemma licenses direct sums in the common coefficient universe; the total-complex definition gives the sign (-1)^p. Step 5 proves strict transition equations on generators, rather than asking a derived isomorphism at each n to supply missing coherence. Both equations remain linear after the prescribed scalar restrictions. Step 6 verifies the finite reductions are K-flat with flat terms and invokes only the derived-pullback and total-tensor computations those nodes actually state. Exact scalar restriction is cited explicitly.

Step 7 invokes the actual functor on the derived category of strict towers, whose statement is stronger than existence of a Roos triangle. Step 8 checks the two finite augmentation maps and then the diagonal cone map with zero shifted-product component; def-weil-strict-roos-model explicitly defines these coordinates and maps. Step 9 uses the exact-countable-product theorem for an arbitrary ring sheaf on a scheme's pro-etale site, and the strict Roos derivation theorem to compare the normalized cone to derived strict-tower limit. I checked its site, universe, sheafification and derived-category hypotheses: choose a larger common universe for the already chosen small sites and coefficients. No pullback/product commutation is asserted. Step 10 checks naturality on maps of flat-term K-flat complexes, inversion of quasi-isomorphisms, and the descent hypotheses: right calculus of fractions for quasi-isomorphisms, enough resolving representatives, and the full surjective complex-to-homotopy quotient. The existing resolving-representative restriction theorem makes the natural comparison unique. The ordinary and finite operation comparison statements provide the requisite natural computations and independence.

Small cases checked: f the identity gives scalar reassociation; the empty scheme has the zero ring sheaf and every formula is its unique map; zero complexes make both towers zero; degree-zero free modules give the ordinary scalar-association formulas; and arbitrary positive n, including n=1 and adjacent reductions, satisfy the explicitly written transition calculation. For two-sided unbounded U,V, totalization uses direct sums only, which scalar extension preserves; no finite sum assumption enters. No new hypotheses of completeness, constructibility, qcqs, cohomological flatness or boundedness have slipped in. Each non-elementary proof step is shorter than 2000 characters. I corrected the initial descent explanation to cite the existing calculus-of-fractions and resolving-representative theorem explicitly instead of leaving restriction-to-K-flat localization implicit. No mathematical statement dispute remains.

## Unfinished

None in the one-level split. All downstream unresolved theorems remain existing nodes, without fabricated proofs or Lean changes.
