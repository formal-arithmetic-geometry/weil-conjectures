# Stage-1 delivery: lem-sfb-nodal-numerical-very-ample

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-nodal-numerical-very-ample.json`: item, statement, split; no Mathlib match.
- `citations.json`: every step/node incidence, quoting the actual cited statement verbatim.
- `report.md`: this report. `searches.jsonl` is the unmodified search-command log.

New nodes: 0. Mathlib leaves: 0. No unit file is changed: the item is a supporting lemma, not the unit statement.

## Attachments

None. I searched the whole project source under lean/WeilConjectures for the item tag and for nodal/numerical very ampleness. The relevant numerical declaration in AlgebraicGeometry/Curve/RiemannRoch.lean is `AlgebraicGeometry.Scheme.isVeryAmple_of_degree`, line 1590, but its section imposes smooth relative dimension one. It does not prove the reducible nodal item. I also read the adjacent dimension-drop criterion, which has the same smoothness restriction. No declaration stating this item was found.

## WANTED

WANTED: Franciosi and Tenni, *The canonical ring of a 3-connected curve*, Rend. Lincei Mat. Appl. 25 (2014), pp. 37–51, Section 2, Proposition 2.5(iii), printed p.40, for lem-sfb-nodal-numerical-very-ample; local PDF absent. I read the author-hosted primary PDF at https://pagine.dm.unipi.it/franciosi/lavori/franciosi-tenni2.pdf . Its proposition records exactly this numerical very-ampleness conclusion. This delivery instead follows the locally available Stacks proofs, so no missing PDF is needed to check its proof.

## Findings and changes

The statement is unchanged, with every original field, citation, provenance and logged historical search retained. It is true and needs no STATEMENT-DISPUTED correction. The new proof does not assume that a length-two subscheme at a node is Cartier, or that the curve is smooth or integral. It uses no SGA source. The nodal restriction is stronger than what the existing reduced-curve obstruction needs; it is retained faithfully.

The imported item had no proof. Searches by numerical very ampleness, subcurves, length-two schemes, the Stacks labels and tags, and the whole-blueprint `blueprint_refs.py search` for “very ample”, “0E3E”, and “numerical” exposed existing usable nodes. The smooth-curve numerical and separation lemmas are not applicable. The generic point-and-tangent criterion is applicable. Consequently no new lemma is warranted: creating a numerical vanishing lemma here would merely package a few lines of the contradiction already proved in step 2.

I read the three levels in SETUP.md, the chapter and unit records, and the latest blueprint's unit statement and direct-image proof. The item is a remote supporting prerequisite in the long existing alteration/stable-curve linear-series branch, not a new replacement of a chapter or unit argument. Its existing blueprint.from provenance and null ancestor are retained; blueprint_refs.py ancestor confirms None. The split_report names the argument supplied here. Generic off-unit geometric and module-cohomology tools are declared in split_report.tool_uses for the maintainer to assess.

## Not duplicates

No new nodes are created, so there are no new/existing same-tag pairs. Existing 0E3E and 0E8S results are cited directly; the smooth 2g+1 lemma is not copied or generalized as a new node.

## Review by NB

I read delivery-errors.md B–E in both copies and checked this split against the mathematical failures they describe. For the item's source I read Franciosi–Tenni Proposition 2.5(iii) in its author PDF. For the proof I read Stacks curves.tex Tag 0E3E, `lemma-vanishing-on-gorenstein`, including its dualizing-map proof; the length-two restriction argument in Tag 0E8X, `lemma-tricanonical`; and varieties.tex Tags 0E8T and 0E8S, `lemma-variant-separate-points-tangent-vectors` and `lemma-separate-points-tangent-vectors`. I read the complete statements of every cited DAG node, rather than borrowing an assertion from inside its proof. There are no new nodes requiring source or hypothesis review.

Step 1 uses lem-pc-projective-proper for precisely projective implies proper, lem-trf-proper-field-invertible-coherent for Noetherianity of a proper scheme over a field, and lem-pc-zero-dimensional-closed-subscheme-finite for affineness and finiteness of a zero-dimensional closed test scheme. The hypotheses are exactly the projective field-scheme and invertible module supplied by the item. In particular the first node is not restricted to smooth curves. The test scheme's degree is its finite k-algebra dimension; no reducedness of the test scheme is assumed.

Step 2 uses the statement, not the proof, of lem-sfb-curve-ideal-h1-subcurve-obstruction. All its proper, reduced, connected, dimension-one and invertible hypotheses hold, and it allows arbitrary zero-dimensional test schemes. Its B is connected reduced of dimension one. In a Noetherian pure one-dimensional ambient scheme its one-dimensional components must be ambient components, and an extra isolated point would disconnect B. Thus B is one of the unions quantified over by the item. For the intersection, the affine quotient clause of def-weil-closed-immersion says exactly what is needed: it is Spec(R/J). Its k-dimension is at most dim R by a surjective linear map, including the zero quotient. The numerical contradiction is explicit: the obstruction gives degree at most -2χ+2=2p_a, while the hypothesis gives at least 2p_a+1. No duality or exactness fact is silently inferred from a definition; the substantial obstruction is an existing theorem node.

Step 3 obtains the ideal-twist exact sequence directly in a local rank-one frame, using the actual definitions def-sc-invertible-module, def-sbc-closed-immersion-ideal-sheaf and def-pc-module-pullback. This avoids any unjustified exactness of tensor by an arbitrary module. The only cohomological inference is the exact section-boundary statement of lem-sc-module-section-boundary-exact: when H^1 of the kernel is zero every quotient section has zero boundary and hence a lift. It is Zariski module cohomology on a ringed space, matching the item, rather than the similarly named étale lifting lemma. Global sections of the closed direct image are literally sections on Z.

Step 4 is the explicit elementary argument behind 0E8T. The residue-field theorem applies because X is of finite type over algebraically closed k. The one-point test gives nonvanishing, and the disjoint two-point test gives separation. A nonzero tangent map on an affine neighbourhood has image containing k and ε, hence is onto the dual numbers; it defines a length-two closed subscheme supported at a closed point. Its kernel ideal glues with the unit ideal away from that point. The tangent and closed-immersion definitions used here give precisely those objects. Lifting ε times a local frame gives value zero and derivative nonzero, at a node as well as a smooth point. This uses no unproved identification of all length-two schemes with Cartier divisors.

Step 5 uses lem-sc-point-tangent-separation-closed-immersion exactly as stated, with the full section space V. That node explicitly requires generation at closed points, point separation and tangent separation; step 4 supplies all three, so the single-point caveat noted in that node's source is irrelevant. Its statement supplies finite-dimensionality, the complete-system closed immersion and the tautological pullback, not merely a bare existence of some embedding. Evaluation generation is its explicit condition (0). No unsplit node duplicates a clause of the item.

Small cases checked: P^1 with A=O(3) satisfies the bound; O(2) still being very ample does not contradict this sufficient criterion. Two rational components meeting once with multidegree (3,3) satisfy the component and total bounds. An irreducible rational nodal cubic has p_a=1 and its degree-three hyperplane line meets equality. At a node, any nonzero linear functional on its two-dimensional cotangent space produces the required surjective dual-number map; no smoothness is needed. Empty intersections give dimension zero and only strengthen the contradiction. Disconnected unions B, potentially of negative arithmetic genus, cause no problem because the obstruction supplies connected B and the item quantifies over all unions. Characteristic two causes no division by two in this argument.

Every non-elementary fact is a cited theorem node. Only the explicit quotient, local-frame and dual-number computations are treated as elementary. No proof step exceeds 2000 characters. proof_deps is exactly the union of uses, and every citation quote is copied verbatim from the live cited statement. New Mathlib searches were run with the prescribed command and recorded without altered queries; returned Proj properness and Weierstrass or affine-space facts are not a match. The second semantic phrasing also found no match.

## Unfinished work

None at stage 1. The existing prerequisites remain separate DAG obligations; this delivery does not assert that their Lean proofs are finished.
