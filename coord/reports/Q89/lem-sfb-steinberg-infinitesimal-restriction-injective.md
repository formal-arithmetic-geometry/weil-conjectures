# Q89 stage-1 delivery

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-steinberg-infinitesimal-restriction-injective.json: item, statement, split; not in Mathlib.
- dag/nodes/sec-six-functors-basics/lem-sfb-frobenius-borel-induction-geometry.json: new statement-only node, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-steinberg-borel-thickening-extension.json: new statement-only node, unsplit; no Mathlib match.
- citations.json: verbatim statement evidence for each proof-step citation.

## Attachments

None. Searched the live lean/WeilConjectures source for the blueprint tag, Steinberg, infinitesimal induction and restriction terminology. The Steinberg hits there concern Lang--Steinberg for semilinear maps; no declaration states this item. No Lean was written or compiled.

## Sources wanted

WANTED: J. C. Jantzen, Representations of Algebraic Groups (2003), Part II 3.18--3.19, for the item and lem-sfb-steinberg-borel-thickening-extension. No local book exists; I do not claim to have read those pages.

WANTED: Masaharu Kaneda, On the Frobenius morphism of flag schemes (1994), Sections 2.3--2.5, printed pp.320--323, for both new nodes and the item's assembly. Read the primary paper online at https://msp.org/pjm/1994/163-2/pjm-v163-n2-p07-s.pdf; no copy was downloaded into the repository. Section 2.3 gives regular-function induction, adjunction and tensor identity; 2.4 gives transitivity; 2.5 gives the Frobenius quotient and, in (9), extension of the infinitesimal Steinberg module to G. In particular the extension claim is present in the primary paper; no claim is made that Kaneda explicitly proves the item's exact restriction map.

## Corrections and scope

The item's statement is unchanged and is not disputed. The initially empty proof is replaced by an explicit restriction-kernel argument. The extension lemma concerns functions on H_r = (F^r)^{-1}(B^(q)), not global sections on S. The other new lemma concerns the quotient S/H_r and restriction from H_r to L_r. Neither is the conclusion of the item. The module extension remains a genuine statement-only input: its proof cannot be inferred just from simplicity on L_r.

The ancestry helper prints a null blueprint ancestor for this imported-created chain. I retained that null and the complete inherited via chain, with exact places filled in. Whole-blueprint searches for Steinberg, infinitesimal induced, Borel thickening, Frobenius Borel, induction and Frobenius finite did not find an equivalent blueprint statement. The sole Steinberg blueprint match is the unrelated semilinear Lang--Steinberg lemma. Source-level searches used the latest blueprint, not a historical snapshot.

The proper-global-functions lemma is declared as a generic off-unit tool in split_report.tool_uses. It supplies only the degree-zero constant-function assertion for the proper reduced connected quotient, not a proof route through proper base change. I checked its statement and dependency closure; it does not reach this item, Kempf vanishing, or the induced Weyl dimension formula. No use is made of lem-sfb-steinberg-induced-module-irreducible, the Weyl dimension formula, Kempf vanishing, or any SGA source.

## Not duplicates

lem-sfb-frobenius-borel-induction-geometry vs lem-sfb-steinberg-infinitesimal-restriction-injective: the new statement identifies the Frobenius Borel quotient and restriction of functions from H_r to L_r for every B-character; it asserts no injectivity of restriction from S at a Steinberg weight.

lem-sfb-frobenius-borel-induction-geometry vs lem-sfb-reductive-frobenius-twist: the existing node states faithful flatness and root-data compatibility of G to G^(p); it does not identify the Borel preimage quotient or induced-function restriction.

lem-sfb-frobenius-borel-induction-geometry vs lem-sfb-reductive-borel-pair-structure: the existing node supplies the ordinary Borel quotient G/B, not the quotient by the nonreduced Frobenius thickening or the H_r-to-L_r restriction isomorphism.

lem-sfb-steinberg-borel-thickening-extension vs lem-sfb-steinberg-infinitesimal-induced-simple: the existing sibling states simplicity of the L_r-module. The new node states extension of the H_r-module action to S, and asserts neither that simplicity nor any restriction map from E_r.

lem-sfb-steinberg-borel-thickening-extension vs lem-sfb-steinberg-infinitesimal-restriction-injective: no sections on S, injective map or global induced module are mentioned in the new conclusion; its input is the independently constructed module of semi-invariant functions on H_r.

lem-sfb-steinberg-borel-thickening-extension vs lem-sfb-steinberg-weyl-restricted-freeness: that existing node concerns the dual global-section module at r=1 and restricted enveloping algebra freeness; the new input concerns extension of the infinitesimally induced module on H_r for every r.

## Review by Q89

I read the worker brief, stage-1 contract, all delivery-errors B--E (including the duplicate historical copy), SETUP's three-level route and GOAL. The chapter and unit records were read before the item statement; this supporting item is not the unit's key statement, so no unit fields were changed. Its parent's landed review expressly requires the pre-Kempf II.3.18--3.19 route to avoid the earlier cycle. I kept that route.

For the item I read Kaneda Sections 2.3--2.5 online, in particular the displayed induction conventions, the quotient diagram and the Steinberg extension assertion (9). For the geometry node I read the same quotient and infinitesimal coordinate description: its restriction assertion is the subgroup product H_r=L_r B with intersection P_r, formulated as regular-function descent rather than a claim about rational points. For the extension node I read (4)--(9), especially the explicit assertion of a G-module structure. Kaneda takes Lie(B) roots negative relative to his positive system. Our positive system is Lie(B), so his rho is minus our rho and his inducing character is -(q-1)rho. His inverse-character covariance is therefore exactly the positive power displayed here. I have not silently replaced an H_r-action by an action merely of geometric points.

Step 1 uses precisely the two new statements: the geometry node says the quotient is proper geometrically integral and gives the L_r-equivariant restriction isomorphism for every character, so substituting chi = rho-tilde^(-(q-1)) is legitimate; the extension node says V_r is finite dimensional and its specified H_r-action extends to S. Every group, character and Frobenius in the hypotheses is the one introduced in the unchanged item. No simplicity theorem is used here.

Step 2 is the elementary regular-function form of induction in stages. I wrote the finite-coefficient tensor calculation instead of citing transitivity as an unnamed theorem. In particular the coefficient equation ensures regularity as a V_r-valued function, and the equation A(ga)=a^(-1)A(g) uses the correct left-translation inverse. There are no node citations in this step and no hidden finite-dimensionality assumption: it was supplied in step 1.

Step 3 uses the geometry statement's actual quotient factorization property, not a theorem inferred from a definition node. I checked that its target is nonempty, reduced and connected, precisely the hypotheses needed in the opened statement of lem-weil-pbc-proper-reduced-algclosed-global-sections-product, together with its properness and the algebraically closed base. That lemma identifies the ring with one copy of F. Taking coordinates in a finite basis of V_r therefore proves constancy of the vector-valued map. The formula C(ga)=ga(a^(-1)A(g))=gA(g) and evaluation at 1 were written out. This is the tensor-identity argument, not an unproved assertion that two induction functors are isomorphic.

Step 4 uses the actual restriction isomorphism stated by the geometry node to pass from zero on L_r to zero on H_r. Then the explicit formula from step 3 implies f=0. I wrote the scalar-extension equivariance identity for the very same restriction map, proving every clause of the item. All citation entries quote verbatim statements, including the hypotheses actually used; none quotes a proof or paraphrases a conclusion.

I tested the new statements on S=1 (H_r=L_r=P_r=1, quotient a point, all modules F), on SL2 with its upper triangular Borel (the sections are degree q-1 binary forms, restriction has degree less than q in the opposite-root coordinate), on p=2 and r=1, on r>1, and on products. For a general character the H_r-to-L_r isomorphism is valid independently of the Steinberg extension, while the extension lemma deliberately requires the precise Steinberg weight. I did not apply extension at a non-Steinberg weight. Neither lemma requires a false equality H_r(D)=L_r(D)B(D) for every D: the geometry is fppf, so it includes nonreduced algebras.

I checked B1--B10: complete independent statements, introduced notions and definition dependencies, single-escaped TeX, source places, real recorded searches, no unjustified Mathlib leaf and searched blueprint ancestry. I checked C1--C8: the only non-elementary inputs have explicit node citations; the quotations match their statements; no proof-only content is borrowed; the generic off-unit tool is declared. I checked D1--D5: two strictly different supporting inputs, with the kernel and tensor calculations left in the item, no circular identification or unexpanded omitted detail. I checked E1--E7: field characteristic, all-algebra versus point actions, positivity sign, order of factors and inverses, nonreduced subgroup schemes, properness and connectedness. Every step is shorter than 2000 characters. The two new nodes have no proof steps or proof dependencies. All required Mathlib searches, including second semantic phrasings, were run with msearch.py and read; returned abstract-group induction and Lie weight statements do not specialize to this group-scheme theorem. Search outputs are retained in new-node-search-results.json and the official searches.jsonl.

## Unfinished work

No part of this one-level split is unfinished. The two statement-only supporting lemmas remain unsplit as required by the worker contract. Their sources are WANTED locally as stated above. Delivery checks are recorded below when run.
