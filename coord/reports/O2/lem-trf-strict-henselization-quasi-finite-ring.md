# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-strict-henselization-quasi-finite-ring.json`: statement, split; no Mathlib match for the item. Seven proof steps, all using existing DAG nodes. The statement is unchanged.
- `citations.json`: 17 step/node entries containing the full verbatim statements used.
- `searches.jsonl`: actual search-command records, retained as produced. `write_split.py` is a sandbox-only preparation script.

## New nodes

None. Zero new nodes and zero new Mathlib leaves. In particular, neither the finite-local assertion nor the tensor localization assertion has been moved into a child restating a clause of the item.

## Attachments

None. Searches under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint id and strict-henselization/quasi-finite notions found no declaration of this comparison. The proper-curve field-extension file mentions residue fields of two strict henselizations only as motivation, and does not state the item. No upstream master sorry declaration was treated as a proof.

## WANTED

None: all literature used is present locally.

## Audit of the starting node and route

The starting node has no proof and no own Lean audit or declaration. Its statement agrees with algebra.tex Tag 05WR, `lemma-quasi-finite-strict-henselization`: finite type and quasi-finiteness at the specified prime, compatible separable closures inside the geometric field, finite local map, finite purely inseparable residue extension, and the specified tensor localization. The extra explicit finite-type hypothesis is already part of the project's definition of quasi-finite at a prime. The finite-map parenthesis is justified by the existing finite-ring-map lemma. There is no statement dispute and no correction to the statement.

I read the chapter and unit records, the current blueprint proof of `lem-trf-local-term-locality`, and the delivered parent `lem-trf-finite-base-strict-localization`. This item is supporting commutative algebra below the specialization/finite-base argument, not the key node of its unit; no unit realization fields change. Its inherited blueprint ancestry is retained, with the supporting place made explicit. Whole-blueprint searches for `strict henselization`, `quasi-finite`, and `henselian`, and whole-DAG searches for 05WR, 04GH, 04GJ and the comparison notions found the tools reused here. No blueprint node states this entire item in another form, so `same_as` remains empty.

The proof constructs the same localization as 05WR, obtains finiteness and henselianity by the finite-type decomposition (04GJ, yielding 04GH(3)), and identifies it with the target strict henselization. In the last identification I use the existing relative ind-etale assertion and Olivier's local weakly-etale theorem (092Z) instead of introducing new nodes for 08HV and the general uniqueness lemma. This implementation of the uniqueness step is marked `proof_origin.by = agent`; it is not an assertion that every sentence appears in 05WR. These are generic tools below the unit's proof route, declared individually in `split_report.tool_uses`. No SGA source is used.

## Mathlib searches

The new searches are the actual commands recorded in `searches.jsonl`, and their exact tool/query text and returned digests are appended to the item without deleting the inherited searches. Two LeanFinder phrasings returned quasi-finite base-change, residue-field finiteness, and ordinary localization declarations. LeanSearch returned the `RingHom.QuasiFinite` API. I read the pinned `RingTheory/QuasiFinite/Basic.lean`: it does not construct strict henselizations, and its pointwise quasi-finite definition also needs comparison with the isolated-point convention. Grep for strict henselization in the entire Mathlib source returned no hits. The broader henselian grep and the valid Loogle name search led to `RingTheory/Henselian.lean`, which I read: root lifting, local henselian classes, and completeness results do not state this comparison. The initial Loogle query with `IsHenselianLocalRing` failed because that identifier is unknown; it was replaced by the valid `HenselianLocalRing, Module.Finite` query, which returned zero hits. No failed query was used as evidence of absence, and no unavailable service was called a negative mathematical result.

## Review by N2

I read the full statement and proof of Tag 05WR, algebra.tex `lemma-quasi-finite-strict-henselization`, and the relevant statements and proofs of 00PN (`lemma-four-rings`), 04GH (`lemma-finite-over-henselian`, especially (3)), 04GJ (`lemma-mop-up`), 00U2 (`lemma-etale`), 04GP (`lemma-strict-henselization`), and 030K in fields.tex (`lemma-separable-first`). I also read more-algebra.tex Tag 092Z (`theorem-olivier`), and the current blueprint statement and proof of ind-etale stability. There are no new nodes requiring separate source reviews.

For Step 1 I opened `lem-weil-pbc-strict-henselization-functoriality`, whose actual clauses (1)--(3) give strict henselianity, the residue embeddings inside the same Omega, and the canonical local map. I use those assertions, not merely the definition of the colimit. The strict-henselization definition node supplies the stated colimit construction. The tensor evaluation is a direct multiplication formula on pure tensors; its contractions are computed through injective residue embeddings. In particular neither residue field is identified with all of Omega.

For Step 2 I opened the four-rings node: it assumes finite type and a surjection from the base-change tensor product. Here that map is an isomorphism, so both hypotheses hold. It states exactly the finite-type and quasi-finite conclusions taken in the step.

For Step 3 I opened the finite-type henselian decomposition node and the finite-local henselian node. The former really gives local module-finite factors and a residual factor with no quasi-finite prime over the closed point; it is not the finite-over-henselian node that states only the already finite case. I explicitly use the four-rings lemma again on the residual-factor quotient to rule out that factor. I wrote out the orthogonal-idempotent selection of a factor and the finite-dimensional-domain argument showing that the chosen prime is maximal, so localizing that local factor returns the factor itself. Only after obtaining module finiteness and locality do I invoke finite-local henselianity. Thus 04GH(3) is derived in the step from existing statements rather than cited through a node that only states 04GH(1)--(2).

For Step 4 I opened the finite-extension-of-a-separably-closed-field node; its clause (a), not its unique-embedding clause, makes E separably closed. The generators of D descend to a finite K-spanning set of E, so that lemma's finite-extension hypothesis holds. For pure inseparability I separately cite and apply the separable-first node: the separable intermediate field is K by the actual definition node's no-nontrivial-finite-separable-extension clause. This does not incorrectly extract pure inseparability from a source sentence that states only unique embeddings. The henselian terminology definition then gives strict henselianity of D.

For Step 5 I opened the affine-chart ind-etale node, the ind-etale stability node, the principal-localization etale Mathlib leaf, and the ind-etale definition. Applied to the whole affine schemes Spec A and Spec B, the chart node gives the algebra structures used in the tensor formula. The stability statement explicitly supplies base change and composition. Principal localizations of the identity etale C-algebra are etale by the leaf's second clause. I wrote out why their filtered colimit is C_n; no theorem about general prime localizations being finitely presented is assumed. This supplies ind-etaleness over the common base B for both D and H.

For Step 6 I opened the relative clause of ind-etale stability and the precise local weakly-etale strict-local theorem. The map is built as g(r tensor b)=h(r)b, then localized. Its inverse image of the maximal ideal is computed through the given injective map L to Omega; therefore every required denominator is a unit, and the resulting D to H is local. Both algebras are ind-etale over B by Step 5, so the relative clause applies to this particular B-algebra map and implies weak etaleness. D is strictly henselian by Step 4. Those are exactly the hypotheses of 092Z. The resulting isomorphism identifies the original canonical R to H map, rather than producing an unrelated abstract isomorphism.

For Step 7 I opened the finite-ring-map quasi-finite node, whose statement supplies both finite type and quasi-finiteness for the parenthetical case. The main identification is elementary localization algebra: A outside p is already inverted in R; B outside q lies outside n; the two displayed localizations have the same maps and invert precisely the same complement of the induced kernel. I checked both directions of this universal-property comparison. All finiteness and residue assertions transfer along the R-algebra isomorphism of Step 6.

I checked B=A (the localization and comparison reduce to the identity), a finite separable extension of fields (the compatible strict henselizations identify), and a finite purely inseparable extension of an imperfect field in positive characteristic (the finite residue extension can be nontrivial and is retained). The proof also allows a finite algebra with several local factors and nonreduced finite fibres: the chosen geometric point selects one factor, and no reducedness is assumed. A geometric field transcendental over the base residue field causes no issue: only its relative separable closures are used. The zero ring cannot occur as A or B with the specified primes, and D is nonzero since n is the kernel of a unital map to a field. No Noetherian, separability of the original residue extension, or algebraicity of Omega is added.

Against B--E: the only delivered node is self-contained and keeps its statement; no unsplit new node or duplicate is introduced; all cited statements were opened; every non-elementary input is a node citation; the elementary assertions are displayed as tensor or localization formulas and finite-dimensional linear algebra. I checked the full dependency closures of all substantive tools and found no path back to this item. Every step is under 1100 characters, so none triggers the long-step review threshold. During preparation the verbatim-quote assertion caught two inaccurate extracts (a nonexistent phrase in the separable-first statement and an escaped tab in the ind-etale quotation); I repaired the extracts against the actual statements before producing citations.json. No mathematical statement was weakened.

## Unfinished work

No mathematical part is left open in this one-level split. Existing dependency nodes retain their own proof status; no changes to them or to the live repository are proposed. The first full dry run rejected four citation extracts for being shorter than its 40-character minimum. I replaced every citation extract with the full verbatim statement, including its hypotheses, and reran the dry run. The earlier server review_split check passed. Full preflight and delivery results follow from the delivery command.
