# Stage-1 report: lem-per-ordinary-henselian-pointed-neighbourhood-limit

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-ordinary-henselian-pointed-neighbourhood-limit.json`: existing statement node, now split into eight steps, no Mathlib match. Statement unchanged; added the missing statement dependency `def-weil-pbc-localization-at-prime` for its expression A_p.
- `citations.json`: one verbatim statement quotation per dependency of each numbered proof step.
- `searches.jsonl`: five actual searches for the item, in addition to preserving the existing node's inherited search history. All five services/commands succeeded. The two semantic phrasings returned henselian definitions and criteria, standard etale algebras, and individual pointed extensions, not the asserted henselian colimit and spectrum limit. The Loogle and grep searches had no hits.
- No new nodes; no new Mathlib leaves. All write operations are confined to this item sandbox.

## Attachments

None. I searched WeilConjectures in the read-only slopmaster2 source by the blueprint id, henselization/henselisation, and pointed-neighbourhood terminology. The related finite-morphism neighbourhood constructions concern geometric points and do not state this item. The upstream master checkout provides no finished declaration of this item either. No Lean file was written or compiled.

## WANTED

None. The Stacks source files needed for this split are present.

## Findings and corrections

The item statement is true and unchanged. Its source references ordinary, not strict, henselization. Some existing triple-colimit nodes have separable-closure hypotheses, and some old nodes have only a title as their natural-language statement. I did not use those nodes to justify arbitrary-field assertions. Instead I used the existing explicitly arbitrary-field filteredness, unit-refinement and ideal-refinement statements. Specializing their field K to kappa(x) forces the residue-field embeddings to be inverse isomorphisms, as proved in Step 1.

I corrected an error in my own initial sandbox draft before delivery: Spec(A_p) to Spec(A) is not generally an open immersion or etale. For example Z to Q at (0) is not finitely presented, so it is not etale. No such inference remains. The final proof carries out the Stacks 04GN construction directly over A, using residue triples and their existing refinement lemmas. This is a node-level expansion of the stated ordinary-henselian neighbourhood route, not a replacement of a unit or chapter route.

The source field of the original item mentions descent from A_p. The final proof avoids having to assert that localization is etale: it constructs pointed etale A-algebras directly and proves afterwards that the structural map factors locally through A_p. The conclusion and every hypothesis remain the same. This is not a statement dispute.

## Blueprint and route

I read the chapter record sec-deligne-laumon-a1, unit sk-p-dl-a1-perverse, and the current main-20261015 ancestor lem-per-artin-gabber-affine-curve proof, particularly Step 3. The precise henselian passage enters this descendant through the parent lem-per-finite-flat-cd-etale-exchange and ILO II 3.2.3, as recorded in the inherited blueprint.from.place. No chapter or unit record was edited. The item is not the unit's key node. The blueprint searches for henselization/henselian and residue triples and the whole-DAG tag/key-word searches found no blueprint node stating this ordinary residue-preserving system; blueprint.same_as remains []. Generic off-unit lemmas are declared in split_report.tool_uses where required.

## Not duplicates

No new node is proposed. The existing strict-henselization limit and ring-colimit nodes require a geometric point or separable residue closure and do not assert unchanged residue fields. The pair henselization and local-pair comparison do not provide the required pointed A-neighbourhood system. The existing henselization-prime-ind-etale node does not provide the pointings and residue identifications. I reused the smaller existing arbitrary-field triple and category tools rather than creating variants of them.

## Review by Q36

I read Stacks algebra.tex, Tag 04GN, label lemma-henselization, in full, including the filtered pair construction, the unit-localization argument, maximal-ideal calculation, and final simple-root adjunction. The eight final steps give that construction over the original affine base A. I also read the definitions/characterization in algebra.tex Tags 04GF/04GG (definition-henselian and lemma-characterize-henselian), categories.tex Tag 0032 (lemma-directed-category-system), and limits.tex Tag 01YW (lemma-directed-inverse-system-affine-schemes-has-limit). For the named standard-etale construction I read its node statement and Mathlib StandardEtalePair.Ring and homEquiv; these return the quotient and its map to k with exactly the required root and invertible derivative. I read the full natural-language statement of every cited node; citations.json copies those statements, without altering their hypotheses. There are no new nodes requiring a separate source check.

Step 1 uses the definition of arbitrary-field residue triples and the affine-etale essentially-small-cover theorem. The definition explicitly supplies both field maps and their compatibility. I wrote out why k -> kappa(q) -> k being the identity forces both maps to be isomorphisms. The cover theorem supplies a set of representatives; adding a prime and a field embedding adds only set-sized choices, so a small full representative category is legitimate. Representative replacement preserves the stated objects and arrows, not just their isomorphism classes without maps.

Step 2 uses arbitrary-field filteredness (whose statement explicitly says no closure assumption), existence of small algebra colimits, the theorem identifying the filtered algebra colimit with the underlying ring colimit, the colimit universal property, and the cardinal-directed reindexing theorem at aleph_0. I verified that the category is small before using existence and reindexing. The original cocone legs are retained; this matters because the simple-root successor in Step 5 need not be an object literally selected by the reindexing functor.

Step 3 takes only element representatives, unit refinement for b outside q, and ideal refinement for b in q. Each refinement statement has arbitrary K, so it applies to K=k. The resulting argument is elementary relative to those three statements: a ring map preserves a unit, it carries a finite expression in the extended ideal to the same ideal in H, and the cocone equations identify the resulting representative with h. The reverse kernel inclusion follows because the pointing kills p. This proves ker(psi)=pH and invertibility outside it without claiming a stronger strict-henselization theorem.

Step 4 is the explicit elementary fraction/locality calculation using the localization definition. The kernel is proper since psi(1)=1 in the nonzero field k. All elements outside it are units, so every proper ideal lies in it. The map A_p -> H is given by a/s -> rho(a)rho(s)^(-1); its inverse-image maximal ideal is precisely pA_p. Surjectivity to k is established by fractions a/s, not assumed from A -> k (which need not be surjective when p is not maximal). This verifies both the local map and the actual residue-field isomorphism.

Step 5 uses the finite-data theorem on the nonempty directed ring system produced in Step 2, the standard-etale monic derivative theorem, and etale composition. Only finitely many polynomial coefficients are lifted, and monicity is enforced by setting the leading term to 1. In k the prescribed derivative is nonzero and hence a unit, exactly the hypothesis of the standard-etale map theorem. The kernel of E -> k defines a prime over p and a residue embedding, hence a genuine object and arrow of the original triple category. The cocone equation then gives a root of the original polynomial P with exactly residue a_0. I did not use the existing simple-root construction node, which assumes a separable closure.

Step 6 invokes the precise equivalence between simple-root lifting and the finite-algebra idempotent convention of the item's henselian definition. The local-ring hypothesis has already been proved in Step 4. Thus no convention change is concealed in calling H henselian.

Step 7 uses the residue-triple definition, affine-source separatedness, affine-scheme qcqs, and qcqs morphism permanence. The source is affine and the target Spec A is quasi-separated; these are exactly the hypotheses that make an etale morphism of this form finitely presented. Preservation of the closed point follows from inverse images of kernels, and the residue-field identifications were proved in Step 1. No global maximality of p is assumed.

Step 8 uses the small-colimit spectrum-limit theorem, which asserts a limit in all schemes, not merely affine schemes. The diagram and its underlying ring colimit were established in Step 2. I wrote out why the factorization is over X using any projection and the nonempty index. The maximal ideal and residue clauses refer back to Step 4 rather than importing them from an unrelated definition.

For edge cases I checked a field A (p=0, no algebraic closure is forced), a nonmaximal prime such as (0) in Z (the fraction-surjectivity argument is needed), and a nonreduced ring such as k[epsilon]/(epsilon^2) (no reducedness is used). The zero ring has no prime, so it gives no omitted case under the stated x. Non-Noetherian A is permitted at every cited application. Nonempty directedness is established before finite-data and limit arguments. Every proof step has fewer than 2000 characters, so none hides a long inline lemma. I checked delivery-errors B through E: no new statement-only nodes or duplicates, no use of a cited node's proof in place of its statement, no missing closure/size hypothesis, and no cycle introduced by citing the item through one of its descendants. The initial localization mistake was corrected as described above; no unresolved mathematical point remains.

## Unfinished work

None in this one-level split. Existing unsplit dependencies remain their owners' items. The server dry run and push are the final validation and delivery actions.
