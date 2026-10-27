# Stage-1 report: lem-a1-fppf-kernel-pair-quotient-descent

## Files written

- dag/nodes/sec-purity-real-sheaves/lem-a1-fppf-kernel-pair-quotient-descent.json: statement, split into seven proof steps; no exact Mathlib match for the whole statement.
- citations.json: one entry for each of the 16 step/node citations, copying the cited statement verbatim.
- report.md: this report. searches.jsonl retains the prescribed searches as logged; write_split.py is sandbox scratch work.

New nodes: 0. New Mathlib leaves: 0. Existing Mathlib leaves reused: lem-trf-fppf-covering-is-fpqc, lem-weil-pbc-fpqc-representable-descent, lem-trf-fppf-covering-base-change.

## Attachments

None. Searched the live project WeilConjectures source for the blueprint tag, kernel-pair terminology and fppf quotient terminology. The occurrences concern ideal-sheaf functoriality, fibre dimensions and etale descent, not all the clauses of this item. No project declaration states the item exactly.

## WANTED

None. All mathematical sources used are present locally.

## Audit of the imported item

The statement is correct and unchanged. Its original proof was empty. The imported Mathlib searches were retained, with the five searches actually run for this split appended. Two semantic phrasings were used; hits on coherent/regular topologies, scheme morphism-property descent, and generic sheafification do not give the entire scheme statement with its descended base structure. No new definition or lemma is needed: finite locally free already means finite, flat and locally of finite presentation in def-pc-finite-locally-free. In particular, no extra finite-flat-to-fppf node should be created.

The current blueprint ancestor was confirmed with blueprint_refs.py ancestor. The whole-blueprint searches for kernel pair, quotient sheaf, quotient and fpqc revealed no equivalent blueprint node: the quotient-sheaf hit is a mixed direct summand statement. The existing from.node and via list are retained. The current ancestor lem-a1-affine-hc0 proof is the short support argument; the recorded longer geometric chain is supporting DAG material underneath that proof, not a claim that the current blueprint itself contains a fourth paragraph on kernel pairs.

The abelian-group sheafification lemma lem-weil-pbc-site-sheafification-iso-locally-bijective was read and deliberately not cited for this presheaf of sets. Instead steps 6 and 7 prove the universal property directly. Likewise the general Yoneda lemma is not needed: the factorization is constructed section by section.

## Unfinished work

None at stage 1. The existing cited nodes carry the non-elementary descent and covering results. No Lean was written or compiled, no repository or launcher file was changed, and no agents were started.

## Not duplicates

No new nodes were created, so there are no new/existing pairs to compare. The covering comparison, representable fpqc descent, and base-change covering results were reused rather than duplicated. The pointwise relation and the sheaf-gluing construction are explicit elementary proof steps, not restatements deferred to new nodes.

## Review by Q02

I read Stacks groupoids.tex Tag 03C5 (lemma-criterion-quotient-representable), its three conditions and proof, and the statement and opening proof paragraph of Tag 03BM (proposition-finite-flat-equivalence). The latter explains why this criterion is the appropriate final step for the affine finite locally free quotient that created this item. I read descent.tex Tag 023Q (lemma-fpqc-universal-effective-epimorphisms), topologies.tex Tags 022C and 021O, and sites.tex Tag 00WH (proposition-sheafification-adjoint). No SGA source is used.

For step 1 I checked the actual statements of def-pc-finite-locally-free and def-pc-fppf-site: flatness and local finite presentation are in the former, and with the hypothesized surjectivity are exactly the latter's covering condition. The cited existing Mathlib leaf lem-trf-fppf-covering-is-fpqc states the comparison for arbitrary covering families, so it supplies both the singleton case and the item's general clause. The elementary marking refers to this direct unpacking and specialization, not to proving that comparison anew.

For step 2 I checked that lem-weil-pbc-fpqc-representable-descent permits arbitrary target schemes and arbitrary fpqc covering families. I verified the overlap equation by precomposing with the assumed isomorphism k and then cancelling k; no descent datum or target separatedness is assumed. Applying it with target S gives exactly the unique missing structure morphism m. The fibre-product definition supplies its projections and compatibility; the equations also show k is an S-isomorphism after descent.

For step 3 the same two cited lemmas give the representable sheaf equalizer on an fppf cover. I checked the passage to the slice over S explicitly: the structure composite of the glued map and the given H-to-S map agree locally, hence uniqueness of representable descent with target S makes them equal globally. This avoids assuming that absolute gluing is automatically relative gluing. def-weil-pbc-sites-and-cohomology states the sheaf-of-sets equalizer condition used here.

For step 4 I read the whole statement of def-pc-fibre-product. It supplies the unique map from an equal-image pair. Composing it with k inverse produces the required r, with the displayed equation verifying that r is over S. Thus the original image relation really is equality of q-images, not merely its generated equivalence closure. Equality supplies all three equivalence-relation axioms and sectionwise injectivity. Restriction maps preserve the relation by composition, giving a presheaf and a natural map. This is elementary from the assumed isomorphism and that universal property.

For step 5 the statement of lem-trf-fppf-covering-base-change allows every base morphism and arbitrary covering families, in the prescribed universes. Applying it to the already established covering q and f:H-to-M gives the specified singleton covering p. The second projection is the lift by the fibre-product equation; the relative structure equation was checked, so it is an element of U(T) over S.

For steps 6 and 7 I checked the sheaf-of-sets equalizer sentence of def-weil-pbc-sites-and-cohomology and the universal-property definition in def-weil-pbc-sheafification. On the double overlap the two classes have the same q-image, hence are actually equal by step 4, before applying alpha. The sheaf axiom gives existence and uniqueness of x_f. Naturality is verified on the canonical pullback covering for fg and then follows from uniqueness of gluing. The same equality-of-images calculation proves beta composed with iota equals alpha, and uniqueness is checked after the very same cover. These are direct applications of the defining equalizer, with the maps and equations written out; no unquoted local-bijection/sheafification theorem is hidden here. The last citation def-weil-size-convention fixes universes and a small skeleton, not a separate mathematical existence lemma. Every step is under 900 characters, so none crosses the 2000-character review threshold.

For edge cases, when M is empty, surjectivity forces U empty and the kernel-pair isomorphism forces R empty. The unique structure morphism and the empty-domain sheaf condition still give the same argument. For q the identity, the relation is equality and the canonical map is already an isomorphism. For a nontrivial finite faithfully flat field extension, global lifts may fail, but the canonical base-change covering has a lift, exactly as required; no false global-surjectivity assertion was made. Arbitrary disconnected or nonreduced schemes require no extra argument because the proof uses morphism sets and the scheme fibre product, not the underlying point sets. In particular no positive constant degree, no separatedness, and no affine hypothesis was introduced.

I checked delivery-errors B through E point by point: self-contained unchanged statement, single TeX escaping, exact source tags, no artificial nodes, no changed maintainer fields, cited statements actually supplying each non-elementary use, no use of proofs in place of statements, and no dependencies through the parent quotient node (which would create a cycle). citations.json is copied verbatim from those opened statements. No statement correction or unresolved mathematical issue remains.
