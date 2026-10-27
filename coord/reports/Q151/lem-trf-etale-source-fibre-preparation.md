# Worker report: lem-trf-etale-source-fibre-preparation

## Files written

- dag/nodes/sec-trace-formula/lem-trf-etale-source-fibre-preparation.json: statement, split into six proof steps; no exact Mathlib match for the assembled statement. No new nodes and no new Mathlib leaves.
- citations.json: one verbatim statement quotation for each of the twenty step/node citations.
- searches.jsonl: actual search-command results, retained unmodified; prepare.py is sandbox-only preparation code.

## Attachments

None. Searched lean/WeilConjectures/ for the exact blueprint tag and for source-fibre, source-cover and flat/finitely-presented source-descent terminology. The existing single-map source-descent declarations do not state the whole item, so they do not qualify as attachments. Mathlib supplies separate ingredients rather than the assembled source-cover and specified affine-fibre assertion.

## WANTED

None. All mathematical sources used are available in literature/stacks-project/.

## Corrections and scope

The item statement is unchanged. Its former proof was empty. The source Tag 0C5D reduces nodal locality to flat/finite-presentation source descent and then fibres; this delivery supplies exactly that structural and fibre-preparation input. It neither asserts nor proves nodality. Its inherited blueprint ancestry records the historical semistable auxiliary branch. Read the current latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md and .proof.md: the current trace-level proof is by contracting correspondences. This generic scheme tool makes no change to that unit route or to the chapter. No SGA source is used.

DAG and blueprint searches found the needed ingredients already present. Searches included the Stacks tags 036K, 036N, 05G5 and 01T6, key phrases about source descent and geometric fibres, and blueprint_refs.py searches for finite presentation, etale covering, flat source, fibre product of affine, source-cover, geometric-fibre preparation and 036N. No standalone blueprint node states the whole item. No new fact is created merely to restate a clause, and no new nodes require duplicate comparisons.

## Not duplicates

No new nodes. Reused the existing fppf-source finite-presentation locality, local flat faithful-flatness, scalar-extension flatness reflection, etale covering base change, affine fibre-product, ring finite-presentation base change, and local Noetherian ascent statements.

## Unfinished work

None in this one-level split. Existing cited nodes remain responsible for their own proofs. This stage writes no Lean and invokes no compiler or build.

## Review by Q151

I read curves.tex at lemma-nodal-family-etale-local-source (0C5D), including its explicit references to the source-locality results and its reduction to a field. I read descent.tex at lemma-flat-fpqc-local-source (036K) and lemma-locally-finite-presentation-fppf-local-source (036N). For the affine preparation I read schemes.tex at lemma-fibre-product-affine-schemes (01I4) and lemma-base-change-immersion (01JY); algebra.tex at lemma-base-change-finiteness (05G5), including the polynomial presentation preceding it; morphisms.tex at lemma-locally-finite-presentation-characterize (01TQ) and lemma-finite-type-noetherian (01T6). I also read the faithful-flat scalar-extension statement lemma-flatness-descends-more-general (0584), and the local-flat faithful-flatness statement lemma-local-flat-ff. No new nodes were created, so there are no additional new-node sources to review.

For step 1 I opened def-weil-etale-morphism and def-weil-flat-morphism: the former really supplies flatness and local finite presentation, and the latter measures flatness on exactly the local rings used here. The statement of lem-weil-pbc-flat-ring-map-comp applies to that ring tower, so the forward implication does not assume a global surjection.

For step 2 I opened lem-weil-pbc-flat-local-hom-faithfully-flat and lem-trf-flatness-faithfully-flat-extension. The first requires a flat local map; stalk maps have locality and h_i gives flatness. Joint surjectivity supplies a lift of each x. The second compares N and E tensor_B N over the original base A, exactly what is needed with N=B. I wrote the multiplication isomorphism and its inverse so the argument does not confuse descent under base change of the target with precomposition on the source. The composite A to E is flat by the actual hypothesis on fh_i.

For step 3 I read the entire statement of lem-trf-lfp-fppf-source-locality. Its arbitrary jointly surjective flat locally finitely presented family hypotheses are all supplied here; its equivalence is independent of flatness of f. It imposes no quasi-compactness and includes the empty family case. Thus this use does not replace the etale assertion by a singleton source-descent result that would need an unproved coproduct construction.

For step 4 I read def-pc-fibre-product and lem-weil-pbc-etale-covering-base-change. I wrote both comparison maps, their projections and the uniqueness argument for their composites. This proves an isomorphism over C, not only an abstract isomorphism of schemes. The covering theorem explicitly includes joint surjectivity after an arbitrary base change; no assumption on the geometric fibre being nonempty is added. The exchange of factors is another direct application of the same universal property.

For step 5 I read each of the five cited statements: lem-weil-pbc-affine-opens-basis really refines any given open neighbourhood; lem-weil-pbc-lfp-affine-opens-finite-presentation applies to every compatible pair of affine opens; lem-weil-pbc-open-immersion-base-change gives the open embeddings into the fibre; lem-weil-pbc-fibre-product-affine-spectra supplies the tensor algebra and both projections; and clause (1) of lem-weil-pbc-finite-presentation-base-change-composition gives finite presentation after the arbitrary ring map R to Omega. The projection from C lands in f^{-1}(V), so these inverse-image opens cover C. Applying precisely the same assertion to fh_i, whose local finite presentation is established in step 3, covers D_i. No intersection of two affine opens is assumed affine.

For step 6 I read def-weil-pbc-finitely-presented-algebra, def-weil-finite-type-morphism, def-weil-pbc-noetherian-ring, pqf-def-locnoeth and pqf-lem-locnoeth-lft. Finite presentation gives a displayed finite generating set, so the local finite-type conclusion follows from the actual charts. I checked Noetherianity of Omega directly using its two ideals before applying the locally Noetherian ascent theorem: no Noetherian hypothesis on S is smuggled in. The field spectrum has only the empty and whole opens, so the affine cover proves the finite-type definition as stated, including its target-open quantifier. Empty affine fibres allow the zero algebra, which has a finite presentation when it occurs here. Empty sources, empty fibres and I empty with X empty leave all pointwise arguments and covers valid. Infinite covers of non-quasi-compact sources require no finite subcover anywhere.

Against delivery-errors B--E: the statement is self-contained and unchanged, all proof dependencies are genuine statements used with their stated hypotheses, citations.json copies their statement text verbatim, and no definition is used as a substitute for a non-elementary theorem. The universal-property calculation, finite generators and field-ideal calculation are written out inside steps. Each step is shorter than 2000 characters; no long comparison lemma is hidden. There are no new nodes, hollow definitions, weakened clauses, unlogged searches, or forbidden SGA references. I read the Mathlib search hits and the actual FinitePresentation.lean:45--106, Etale.lean:138--148 and Noetherian.lean:239--250 sources. These justify retaining the assembled item as a split, with the existing Mathlib ingredient leaves reused.
