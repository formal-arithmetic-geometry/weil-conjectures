# Worker report: lem-sfb-dvr-flat-generic-subgroup-closure

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-dvr-flat-generic-subgroup-closure.json: statement unchanged; eight-step split, reusing existing nodes. The full assertion is not a Mathlib leaf.
- citations.json: 26 entries, one per step/node pair, quoting the cited statements verbatim in full to retain the hypotheses.
- searches.jsonl: actual msearch.py results for the item, including two different semantic questions. Existing search entries in the item are preserved, and this run's queries appended.
- report.md: this report. write_split.py is sandbox-only preparation, not a delivered project file.

New nodes: 0. New Mathlib leaves: 0. No Lean was written or compiled. No direct git commands were run, and no repository or launcher files were written.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for schematic closure and flat subgroup concepts. The only schematic-closure mention found was an unrelated compactification comment in Compactification/BaseChange.lean. There is no declaration stating this item's clauses. Mathlib search hits are flatness, generalizing-map and valuative-criterion results, not the claimed subgroup construction.

## Wanted sources

WANTED: Brian Conrad, Reductive Group Schemes, Theorem 5.3.5 proof, printed p.166 (PDF page index 165), https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, local archival copy for lem-sfb-dvr-flat-generic-subgroup-closure. The primary PDF was read online. No literature was downloaded or changed. The proof is marked agent-written because the closure paragraph is expanded here rather than copied as a complete proof from a local document.

## Corrections and scope

The imported statement is correct and has been retained word for word. Its proof was empty. In particular there is no flatness hypothesis on G and none is inserted. The argument only embeds B/I in the generic quotient, never B in B_K. The source paragraph asserts flat subgroup closure and factorization for a flat source but omits these details; the split supplies them.

Read the chapter and unit records and SETUP's three levels. This is a generic algebraic-geometric input within the existing relative-torus closedness chain, not a replacement of a six-functor unit step. blueprint_refs.py ancestor returns None, as already recorded in the node, because the created-item chain reaches no imported blueprint node. Preserved that honest null ancestry and the concrete from.place. Searched the complete imported blueprint for 'schematic closure', 'torsion-free', 'generic subgroup', and 'flat closure'; the closure hits are general Nagata closure statements, not this assertion. Also searched the current latest blueprint text for this group-closure notion. The projective DVR closure node was read: it assumes an embedding in projective space and cannot be applied to an arbitrary separated group scheme, so it is neither cited nor duplicated.

## Not duplicates

No new nodes are proposed. Existing general affine-fibre-product, ideal-subscheme, torsion-free-flat, affine-flatness, finite-presentation and separated/quasi-separated statements suffice. In particular no new node merely restates a clause of the item.

## Review by Q98

I read Conrad's schematic-closure paragraph in the primary PDF, Theorem 5.3.5 proof, printed p.166. It explicitly allows the ambient group to be non-flat before replacement and uses flatness of the source for factorization. I read the relevant local Stacks source: schemes.tex Tag 01I4 (affine fibre products) and Tag 01IN (quasi-coherent ideals and closed subschemes), morphisms.tex Tag 01R8 (kernel schematic image), Tag 01U5 (affine and stalk flatness), more-algebra.tex Tags 0538 and 0AUW (flat implies torsion-free; the converse for a PID), and algebra.tex Tag 00FP (finite type over Noetherian implies finite presentation). The localization criterion's cited source is algebra.tex Tag 00HT. These are the actual ingredients of the expansion. No SGA source is used.

For step 1 I opened all four cited nodes. The affine-fibre-product statement supplies the actual tensor-product ring and projection maps. The closed-immersion statement supplies B_K/J, and the ideal-sheaf statement supplies localization compatibility for the given generic ideal. The quasi-coherent-ideal/closed-subscheme statement supplies the constructed quotient charts. I wrote out the fraction test ensuring contraction commutes with localization, including when B has R-torsion. Thus the source's kernel is the ideal constructed, not an unrelated topological closure. No projectivity or reducedness is assumed.

For step 2 the affine-fibre-product node identifies generic base change. The rest is the explicit extension/contraction calculation: b/r in J implies b/1 in J, so b is in I. This verifies equality as embedded closed subschemes, not just an abstract fibre isomorphism. Its elementary flag refers to this short denominator calculation after citing the affine formula.

For step 3 I checked the DVR definition really supplies the PID condition needed by the existing PID torsion-free-flat lemma. The quotient embeds in a K-vector space, giving torsion-freeness for all nonzero scalars, not only for a chosen uniformizer. The affine-local module criterion is applied with the module equal to its affine coordinate ring; it explicitly gives flatness over the contracted base prime's local ring. The flat-morphism definition is then exactly the asserted stalk condition. This checks the algebra-to-scheme passage rather than assuming it from the definition alone.

For step 4 I checked that the affine-flatness criterion gives R-flatness on every affine W of the open inverse image of V, even if X is not quasi-compact. The flat-implies-torsion-free node has only the domain hypothesis, which a DVR satisfies. The zero-localization test produces a nonzero r killing the pulled-back function; the torsion-free conclusion forces it to vanish before localization. Quotient factorization yields local morphisms, whose uniqueness over the closed inclusion gives their gluing. This proves the universal factorization before it is used to construct any group operations. It is stronger than containment of topological images.

For step 5 the affine product node gives a cover by Spec(A tensor_R D). The affine-flatness criterion gives flatness of both factors. The cited definition of module flatness gives preservation of injections at each of the two tensorings. I explicitly describe the rebracketing isomorphism and its inverse on pure tensors, so no uncited theorem about composition of flat scheme morphisms is used. The existing localization criterion then gives flat stalks of the product. There is no assumption that G, or G times G, is flat.

For step 6 the three sources are C times C, C, and S, whose flatness is established, and the three generic factorizations follow from H_K being a subgroup and step 2. The factorization theorem of step 4 yields all three operations. Every group diagram follows by cancellation of the closed inclusion, with associativity's two maps and the unit/inverse diagrams specified. The elementary flag is justified by applying the already proved result and the group diagrams in the hypotheses; this step hides no new subgroup-closure lemma.

For step 7 the finite-type definition gives a finite affine cover of G with finitely generated coordinate algebras, whose quotients remain finitely generated. The separatedness definition says precisely that Delta_G is closed. I spell out why Delta_C is its base change, using monicity from step 4, and give the affine quotient calculation proving stability of a closed immersion under this base change. The existing separated/quasi-separated lemma gives exactly the final quasi-separatedness assertion. Step 8 then uses the DVR's principal ideals for Noetherianity and the finite-type/Noetherian algebra lemma for finite presentations of those actual quotient rings; the cited finite-presentation definition includes both quasi-compactness and quasi-separatedness, already verified.

The one non-leaf off-unit tool use is lem-pc-affine-flat-module-local-criterion. It is declared in split_report.tool_uses for the maintainer's review: a generic commutative-algebra localization fact, not a new route for the unit. Other off-unit nodes cited are Mathlib leaves. I read every cited node's statement; citations.json copies those statements, not their proofs.

I checked delivery-errors B--E individually: no new underspecified statements or missing searches; no citation used for more than its statement; every non-elementary input is named; no clauses moved to new nodes; factorization precedes group operations, avoiding circularity; all finite-presentation hypotheses are proved. There are no steps longer than 2000 characters (maximum 1125), and no separately assumed inline comparison lemma.

Small cases: when the ambient additive group is Spec(R[x]/(pi*x)), its generic group is trivial and the kernel closure is Spec R cut out by x; thus vertical torsion in G is correctly discarded. Taking a closed-fibre point x=1 shows why the source X must be flat for the factorization clause. In equal characteristic p, the subgroup alpha_p in the generic additive group closes to Spec(R[x]/(x^p)); the proof retains its nilpotents. If G is already flat and H_K=G_K, torsion-freeness forces I=0. The identity subgroup closes to the identity section in a separated G. Localization calculations also handle zero chart rings and empty intersections without assuming a generic point in every chart. No excellence or finite-presentation hypothesis on a test source X was used.

## Unfinished work

None for this one-level split. No new nodes require separate searches or proofs. The maintainer's independent review remains the acceptance step after delivery.
