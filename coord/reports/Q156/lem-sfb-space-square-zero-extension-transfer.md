# Stage-1 delivery: lem-sfb-space-square-zero-extension-transfer

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-square-zero-extension-transfer.json: item, split into five proof steps; statement unchanged; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-naive-cotangent-quasicoherent.json: statement-only lemma, unsplit; no Mathlib match after both semantic searches, Loogle, source grep and a second semantic phrasing.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-module-pullback-quasicoherent.json: statement-only lemma, unsplit; no Mathlib match after both semantic searches, Loogle, source grep and a second semantic phrasing.
- citations.json: verbatim statement quotations for each citation of each item step.

## Attachments

None. Read-only project searches for the blueprint tag, square-zero extension equivalence, naive cotangent and quasi-coherator terminology found no project declaration proving the item. Ring-level dual-number and derivation declarations are different statements. The existing Mathlib leaf lem-weil-pbc-derived-single-fully-faithful is reused.

## Wanted literature

None. All sources used are present under literature/stacks-project/.

## Findings and corrections

The item statement is faithful to Tag 0D3Q and its setup. Its universal derived-Hom test suffices directly, without introducing a derived coherator. Neither kernel sheaf is assumed quasi-coherent. No statement correction or STATEMENT-DISPUTED finding is needed.

The short final inference in the source's proof needs justification: an equivalence on unrestricted extensions does not by itself establish essential surjectivity on the subcategories having a prescribed base-ideal map. Step 3 proves the required injectivity on maps out of f^{-1}J, and step 5 applies it. This uses f^*J as a quasi-coherent test object; it does not assert that u is a monomorphism of all module sheaves.

The unrestricted extension argument reuses lem-sfb-etale-algebra-extension-ext, whose statement includes the natural classification by Ext^1 and the natural automorphism identification by Ext^0. No new node restates the unrestricted-transfer assertion or the item's conclusion. The two new nodes are geometric quasi-coherence inputs independent of extension categories.

The inherited blueprint.from.node is null: tools/blueprint_refs.py ancestor prints None for this ancestry, through the existing proper-space-effectivity chain. This is retained, not replaced by an invented ancestor. The precise inherited place and via chain are retained and extended for the two new nodes. The latest blueprint chapter, unit, and direct-images proof were read. The latest direct-images paragraph no longer expands the historical alteration argument recorded in the inherited ancestry; this split supplies its existing lower-level Stacks input and changes no chapter or unit statement or route. Whole-DAG and blueprint_refs searches for square-zero, cotangent, naive cotangent, quasi-coherent, algebra-extension and 03GA yielded no duplicate of the new statements. The blueprint keyword hits concerning affine algebra cotangents, ringed spaces or finite-presentation space morphisms have narrower/different domains.

## Unfinished work

The two new nodes are intentionally unsplit statement-only tasks for later workers. No required part of the item's assembly proof remains unwritten. No Lean was written, no compiler or Lake tool was run, and the shared repository and launcher were not changed.

## Not duplicates

lem-sfb-space-naive-cotangent-quasicoherent vs lem-sfb-space-naive-cotangent-coherent: the existing result assumes a locally Noetherian target and a locally finitely presented morphism and concludes coherence; the new result asserts quasi-coherence for every space morphism. Those hypotheses cannot be supplied for Z to B prime here.

lem-sfb-space-naive-cotangent-quasicoherent vs lem-sfb-space-naive-cotangent-finite-local-model: the existing result assumes local finite presentation and provides a local finite-type two-term model; the new result imposes no finite-presentation assumption and only concludes quasi-coherence of cohomology. Its generality is necessary in the item.

lem-sfb-space-module-pullback-quasicoherent vs lem-weil-pbc-module-pullback-quasi-coherent: the latter is for schemes and their ordinary module sheaves; the new statement is for algebraic spaces and small etale module sites.

lem-sfb-space-module-pullback-quasicoherent vs lem-pc-ringed-space-tensor-pullback-qcoh: the latter concerns ringed topological spaces, not small etale ringed topoi of algebraic spaces. No local-site comparison is a one-line specialization of its statement.

## Review by Q156

I read defos.tex Tag 0D3Q, including the preceding definition of the fixed-c extension categories, and Tag 0D3P and its proof. I also read the cited deformation descriptions 08UG (lemma-huge-diagram-ringed-topoi) and 08UK (lemma-choices-ringed-topoi); the existing extension-Ext node already packages the classification and the automorphism naturality needed here. For the new cotangent node I read spaces-more-morphisms.tex Tag 0D0Y (lemma-netherlander-quasi-coherent), which explicitly allows any morphism of spaces; its conclusion is about cohomology, not quasi-coherence of the generally enormous canonical polynomial terms. For the new pullback node I read spaces-properties.tex Tag 03GA (lemma-pullback-quasi-coherent) and its reference to sites-modules.tex Tag 03DO (lemma-local-pullback). Its module hypothesis is quasi-coherence; neither flatness nor finite presentation is present. These are the exact domains used in the split.

For step 1 I opened lem-sfb-space-first-order-ringed-description: its statement gives the common etale site and quasi-coherence of the square-zero ideal J. I opened def-sfb-space-naive-cotangent-complex for the relative complex and the definition Ext^i = Hom(-,-[i]), and def-weil-abstract-derived-category for the shift convention. The new 0D0Y node applies to h:Z to B prime regardless of its finite-presentation properties. Taking K=N[-i] really tests Ext^i(N,F), and works for i=0,1. Quasi-compactness and quasi-separatedness of Z are retained exactly as in the item; this direct Hom-test proof does not need to invoke coherator existence using them.

For step 2 I opened the full statement of lem-sfb-etale-algebra-extension-ext. It provides naturality of both Ext^1 classification and Ext^0 automorphism groups for every coefficient pushout, with no quasi-coherence restriction on the coefficients. That is sufficient to prove the Hom bijection explicitly: first use degree-one injectivity to choose a source isomorphism, then lift the target automorphism uniquely by degree-zero bijectivity. I included the case of empty Hom sets and justified that all extension morphisms fixing the ends are invertible. I did not take a Hom-torsor assertion from the proof of a node whose statement only gave its automorphisms.

For step 3 I opened def-trf-space-etale-module-functors for the precise tensor pullback, def-pur-sheaf-tensor-product for its sectionwise tensor followed by sheafification, and the full statement of lem-weil-pbc-derived-single-fully-faithful. The module-sheaf category here is abelian by its existing definition and the fixed relative universes. The new 03GA node applies because J is quasi-coherent on B. I wrote the two inverse tensor formulas instead of using an unstated adjunction theorem to identify maps from f^{-1}J. These formulas commute with restrictions and with u, so derived-Hom injectivity transfers to exactly the required underived map set.

Steps 4 and 5 are elementary assembly from those results. I checked the pushout kernel relation i_F(x) mapping to i_G(ux), which proves c_{u_*E}=u c_E, and checked that extension isomorphisms preserve the induced base map. Thus the fixed-c subcategories really are full subgroupoids, and the unrestricted lift of D has c_E=c by the injection of step 3. No additional obstruction-vanishing or existence theorem is invoked in these two steps.

I checked small cases: identity u gives the identity equivalence; J=0 makes the fixed-map condition vacuous; Z empty gives the trivial sheaf situation. For the cotangent input, an identity morphism has zero cotangent cohomology, while arbitrary affine ring maps give the familiar quasi-coherent H^{-1} and H^0 without finiteness. For the pullback input, zero modules and identity maps behave as stated, and a nonflat affine base change still preserves quasi-coherence (it need not preserve an injection, a claim the node does not make). If either fixed-map subgroupoid is empty, step 5 forces the other to be empty too; the proof does not assume a split B-prime extension satisfying a possibly nonzero c exists. I checked both new nodes against the no-elementary-node, no-duplicate, no-item-clause and Mathlib criteria: they are the independent arbitrary-space geometric input the original source invokes, not renamed transfer conclusions.

All new nodes contain statements only, complete objects and hypotheses, genuine Stacks tags and labels, and exact logged Mathlib queries with the output retained in search-*.txt and searches.jsonl. I read the scheme pullback, general sheaf pullback, Presentation.map and pushforward-quasi-coherence search candidates; the last requires an invertible coefficient-ring map, so it does not give arbitrary tensor pullback quasi-coherence in one line. I checked every citation quote against the cited statement. All proof steps are below 2000 characters, and none conceals a separate comparison lemma. This addresses delivery-errors B through E point by point in the actual statements and argument above.
