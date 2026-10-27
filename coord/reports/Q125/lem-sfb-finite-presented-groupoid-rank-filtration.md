# Stage-1 report: lem-sfb-finite-presented-groupoid-rank-filtration

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-presented-groupoid-rank-filtration.json — statement, split into eight proof steps; no exact Mathlib match. Statement, source, existing search records and ancestry preserved.
- citations.json — 23 verbatim statement quotations, one for each step/node pair.
- report.md and searches.jsonl — review and actual logged searches. No new nodes or Mathlib leaves.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for Fitting/fittingIdeal, groupoid schemes and rank stratification; there is no project declaration giving this item. The existing sorry declarations, and general Mathlib facts about finite morphisms, do not constitute an attachment.

## WANTED

None. All mathematical sources used are in literature/stacks-project/.

## Corrections and scope

The imported statement is correct and is unchanged. Stacks 0ABB, lemma-finite-flat-over-almost-dense-subscheme-addendum, first paragraph, asserts exactly that the Fitting filtration of 0AB9 has finitely presented closed immersions under the added finite-presentation hypothesis. I read 0AB9 (lemma-finite-stratify), Divisors 05P8 (lemma-locally-free-rank-r-pullback), 0C3E (lemma-fitting-ideal-of-finitely-presented), More on Algebra 07ZA(4) (lemma-fitting-ideal-basics), Algebra 0564 (lemma-finite-finitely-presented-extension), and Morphisms 01TV (lemma-closed-immersion-finite-presentation). The affine presentation lemma used is 01TQ (lemma-locally-finite-presentation-characterize).

The existing lem-sfb-finite-groupoid-invariant-rank-filtration states existence but does not specify in its statement that its witnesses are the Fitting subschemes. Consequently I did not cite its proof as though its construction were an available statement. I reused its explicit six-step argument and cited the underlying statements directly, then supplied the additional finite-presentation argument. This avoids a C3/C4 gap. The harmless printed O_S in 0AB9 is replaced in the proof by O_U, as required for the identity summand.

No statement dispute, new node, missing source, chapter change, or unit change. The latest blueprint unit and direct-image proof retain the proper/open reduction. This is the already-recorded 0ABB support lemma of the invariant-affine groupoid prerequisite. blueprint_refs.py ancestor returns null for the existing ancestry, so I retained that value rather than inventing a blueprint ancestor. Searches for Fitting, rank, finite groupoid, invariant rank, and 0ABB found no matching blueprint statement.

## Not duplicates

No new nodes. The nearby existing filtration lemma has no finite-presentation conclusion; this item's proof does not create a second node for that lemma. The existing affine algebra presentation and closed-immersion ideal criteria are reused. In particular no new node was created for the elementary finite-minor computation or for a clause of this item.

## Review by Q125

I read sections B--E of delivery-errors.md in full, both copies, and checked the item against the sources above. Every new prerequisite needed by the argument already has a DAG node; there are no statement-only nodes to review. Every cited node's statement was opened and read; citations.json contains exact portions of those statements, not quotations of their proofs.

Step 1 uses def-weil-finite-integral-morphism for affineness and the finite-type quasi-coherent algebra E=s_*O_R, lem-trf-fitting-ideal-sheaf-pullback for the actual kernel-minor ideals and their closed subschemes, and lem-weil-pbc-quasi-coherent-finite-type-affine(a) for a finite generator bound on each affine. Laplace expansion gives monotonicity directly; the bound is local and proves empty intersection without a global bound. This matches 0AB9 and 05P8(1).

Step 2 uses se=id from def-a1-groupoid-scheme and the affine ideal description in fitting-ideal-sheaf-pullback. I checked the determinant argument: an m-by-m relation matrix annihilates the generator vector, its determinant annihilates every generator, hence 1_B; the split injection A→B makes the determinant zero already in A. This proves I_0=0 without any flatness or reducedness. It is elementary linear algebra, not an unproved Fitting-annihilator lemma.

Step 3 uses the first, hypothesis-free clause of lem-a1-groupoid-source-pullback-translation, with both products projected to their second factor. I checked the source/composition convention and inverse using the groupoid laws. lem-weil-pbc-affine-pushforward-base-change(2) states the algebra comparison for arbitrary base change of an affine morphism; there is no flat-base-change restriction. These two statements really give t*E≅s*E. Step 4 uses the arbitrary-pullback and closed-subscheme clauses of fitting-ideal-sheaf-pullback; isomorphic presentations have identical kernels and thus identical minor ideals. This gives equality of closed subschemes, not merely their underlying sets.

Step 5 uses lem-trf-fitting-ideal-generate-locally(1) on W_r=U minus |Z_r|, so E has at most r generators there. fitting-ideal-sheaf-pullback identifies Fit_(r-1) after restriction. Its image on the quotient defining D_r is zero. The hypotheses of lem-sfb-bounded-generators-fitting-pullback-criterion therefore hold on W_r, and its statement supplies local freeness of exactly rank r after the ordinary pullback. No flatness hypothesis is inserted.

Step 6 uses affine-morphism-permanence(1) and affine-pushforward-base-change(2) to identify the affine structure algebra of the restricted source with that rank-r module. finite-free-algebra-spectrum states finite, flat and locally finitely presented for any finite basis. finite-affine-fibre-sections identifies the fibre with the tensor product, so a basis of size r has fibre dimension r. open-immersion-etale supplies an etale trivializing cover, and finite-locally-free-degree-etale-descent supplies the global degree-r conclusion. I checked the empty-cover case and the fact that the tensor identification is a vector-space identification, not an algebra identification with a product algebra.

Step 7 uses only the explicitly stated finite affine-algebra condition in def-weil-finite-integral-morphism, the affine-open theorem lfp-affine-opens-finite-presentation, the existing Mathlib leaf finite-algebra-presentation-module-presentation, and the finite exact sequence in def-sc-finitely-presented-module. The affine inverse image exists because s is finite, and local finite presentation follows from the hypothesis of finite presentation. Thus the relation matrix is genuinely finite; no Noetherian substitute is used. Algebra 0564, applied to M=B, supplies precisely this implication.

Step 8 uses the same affine Fitting ideal statement and closed-immersion-finite-presentation-ideal. I wrote the actual determinant expansion showing that arbitrary kernel-row minors are generated by the minors of the finite relation matrix. It covers k>p (zero ideal), n≥m (unit ideal), and zero rings. Finite generation on every affine makes the quasi-coherent ideal locally finite type. The closed-immersion criterion expressly includes finite presentation with quasi-compactness and quasi-separatedness of the morphism and imposes no conditions on U. Thus local finite generation does not accidentally prove only local finite presentation.

Off-unit inputs are declared as generic tools in split_report.tool_uses; they are affine algebra, Fitting ideals, and finite-degree descent, not replacements for the unit's direct-image route. The two existing affine finite-presentation inputs are Mathlib leaves. No SGA source or forbidden route is used.

Small cases checked: (i) empty U and zero coordinate rings; (ii) the identity groupoid, with E=O_U, Z_0=U and Z_n empty for n≥1; (iii) a constant group of order d over a nonreduced ring, with Z_n=U for n<d and empty for n≥d; (iv) the group scheme over Spec k[x] with identity component U and an additional involution supported on V(x), whose algebra is A⊕A/(x), so Fit_0=0, Fit_1=(x), Fit_2=A and the rank-one and rank-two strata are D(x) and V(x); this tests a finite finitely presented source which is not flat; (v) an infinite disjoint union of fields with constant finite groups of unbounded orders, testing non-quasi-compact U and the absence of a uniform rank bound. All fit the claimed local argument. If finite presentation of s is dropped, the finite relation matrix need not exist; the proof correctly uses the added hypothesis exactly there.

No step exceeds 2000 characters. The finite-minor expansion is an elementary finite determinant calculation; no comparison lemma or hidden standard argument remains inside a long step. New-node schema, provenance, source-tag, duplicate, clause-restatement and Mathlib-leaf rules are vacuous for new nodes here. The item retains single TeX escapes after JSON decoding, all statement dependencies still occur, proof_deps is exactly the union of uses, and the citation quotations were checked against the current files.

## Unfinished work

None of the one-level split remains unfinished. Its existing non-Mathlib dependencies remain independent queued items as appropriate. Only the required server dry run and push remain at the time this report is first written.
