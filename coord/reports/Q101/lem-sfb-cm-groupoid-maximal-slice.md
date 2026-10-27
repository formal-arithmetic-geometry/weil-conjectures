# Stage 1 worker report: Q101

1. Files written:
   - `dag/nodes/sec-six-functors-basics/lem-sfb-cm-groupoid-maximal-slice.json`: statement, split; preserved the imported statement and provenance, supplied eleven proof steps and searches of the item.
   - `dag/nodes/sec-six-functors-basics/lem-sfb-cm-groupoid-hypersurface-slice.json`: statement, unsplit; no Mathlib match. One dimension drop, with Cohen--Macaulayness only at the distinguished point.
   - `dag/nodes/sec-six-functors-basics/lem-sfb-groupoid-cm-locus-descent.json`: statement, unsplit; no Mathlib match. Descent of the entire CM locus of a saturation to the slice.
   - `dag/nodes/sec-six-functors-basics/lem-sfb-cm-groupoid-double-restriction.json`: statement, unsplit; no Mathlib match. Composition of two restrictions with CM locally finitely presented saturation maps.
   - `citations.json`: one verbatim statement quotation for each of the 44 step/node citations.
2. Attachments: none. The tag search and searches for maximal slices, groupoid slices, and Cohen--Macaulay groupoid assertions in the live `lean/WeilConjectures/` find no declaration stating this item. Existing individual-scheme CM-locus and flat-chart declarations do not assert it. No sorry declaration was counted as a completed proof.
3. WANTED: none; all sources used are available locally.
4. The original node was unsplit, with no proof to repair. Its statement agrees with 04MZ(1)--(4),(6) after the residue-field identification in 04MY. No statement change or dispute was needed. The source's brief equality case and its assertion that properties are immediate under composition have been expanded. A tentative separate CM-base-change node was unnecessary: the existing field-extension, flatness and affine finite-presentation statements supply it in a short step. A tentative immersion-composition leaf was also unnecessary: `lem-weil-pbc-proper-fp-permanence` already has precisely that clause.
5. Unfinished: the three newly created inputs are deliberately statement-only stage-1 queue nodes. No Lean files were written and no compiler, Lake or build was invoked.

## Sources and search record

I read `literature/stacks-project/more-groupoids.tex`, Situation 04MY and the statement and full proof of 04MZ for the item. For the hypersurface input I read 0461, including its affine prime-avoidance/nonzerodivisor construction and the difference between CM at the identity and global CM. For the locus input I read 04LH and 047W(5), including the warning about largest open loci, and `more-morphisms.tex`'s definition of CM at a point and 045U. For double restriction I read 04MW's two cartesian squares and arrow formulas, 04MX and its proof, the final application in 04MZ, and `more-morphisms.tex` 045V. The CM-base-change calculation uses the first, arbitrary-field-extension paragraph of the existing field-extension node; its source is `algebra.tex` 00RJ, which I also read. I do not use its later Noetherian-base consequence.

Every new node has LeanSearch, LeanFinder, Loogle and Mathlib grep records copied from actual entries of `searches.jsonl`. Distinct semantic phrasings were tried. Hits concern smooth charts, manifold structure groupoids, ordinary morphism-property descent, or unrelated stabilizers; none states the scheme-groupoid inputs or a one-line specialization. Whole-Mathlib grep found no CM/groupoid-slice theorem. The exact immersion-composition hit was read, but reused through the existing DAG node instead of duplicating it. The search log is retained unchanged.

I searched the whole DAG by tags and concepts, the imported blueprint with `tools/blueprint_refs.py search` (including 0461, 047W, 04MX, slice and CM-locus terms), and the live project Lean source. No blueprint node states any of the three new inputs. `blueprint_refs.py ancestor lem-sfb-cm-groupoid-maximal-slice` returns null, so the inherited null ancestor is retained, with the item prepended to each new node's via chain. All three have explicit from.place and same_as = [].

The newest blueprint was read under `literature/blueprint/latest/`. The current direct-image proof (3) in `sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md` states the compactification assembly via proper direct image and the open case; it no longer spells out the inherited long alteration/moduli/bootstrap provenance. This split retains that provenance as supplied by the item and addresses its exact supporting Stacks lemma. It neither edits a chapter or unit nor replaces the surrounding route. The generic off-unit algebraic-geometry tools are declared in split_report.tool_uses with their uses and reasons.

## Not duplicates

lem-sfb-cm-groupoid-hypersurface-slice vs lem-sfb-cm-groupoid-maximal-slice: 04MY supplies notation to both, but the new input applies only when d2 > d1 and lowers the dimension by exactly one; it gives CM only at one point. The item proves existence at the final minimal dimension with a globally CM saturation by induction and open shrinking.

lem-sfb-cm-groupoid-hypersurface-slice vs lem-sfb-cm-relation-point-slice: the latter concerns equivalence relations and a quasi-finite saturation, whereas the new node concerns arbitrary groupoids, potentially positive-dimensional stabilizers, and a single dimension drop with only pointwise CM. The relation lemma already depends on this item and cannot be cited back.

lem-sfb-groupoid-cm-locus-descent vs lem-sfb-groupoid-quasifinite-locus-descent: both use 04LH/047W, but the existing node descends the quasi-finite locus with locally finite type hypotheses; the new node descends the CM locus, with flat lfp projections and lfp g. Quasi-finiteness does not imply CM or identify this locus.

lem-sfb-groupoid-cm-locus-descent vs lem-sfb-relation-open-locus-descent: the existing node treats a scheme equivalence relation and the assigned locus of s itself, not arbitrary groupoids with isotropy or the saturation of an arbitrary lfp map g. It cannot be applied to the first immersed slice here.

lem-sfb-groupoid-cm-locus-descent vs lem-sbc-restricted-fibre-cohen-macaulay-locus-open: the existing node gives openness of a fibre CM locus over an open on which the morphism is already flat; the new node also descends the CM locus of the generally nonflat saturation to B.

lem-sfb-groupoid-cm-locus-descent vs lem-sbc-fibre-cohen-macaulay-locus-open: openness for a flat lfp morphism does not supply groupoid invariance or descent to the slice, and h need not initially be flat everywhere.

lem-sfb-groupoid-cm-locus-descent vs lem-sbc-flat-fibre-dimension-near-zero-dimensional-stalk: the existing node gives a constant local-fibre-dimension neighbourhood near a zero-dimensional fibre local ring; it says nothing about descending a saturation's CM locus.

lem-sfb-groupoid-cm-locus-descent vs lem-sbc-flat-fibre-dimension-strata-core: the existing node gives fibre-dense opens with constant dimension; it does not identify a CM locus as the inverse image of an open in B.

lem-sfb-groupoid-cm-locus-descent vs lem-trf-flat-lfp-cm-locus-fibre-dense: the existing node gives density of CM points in each fibre, not descent of a generally nonflat saturation's CM locus along p.

lem-sfb-groupoid-cm-locus-descent vs lem-sfb-flat-relation-cm-open: the existing result finds some CM open in the object scheme of an equivalence relation and a surjective flat saturation; it does not identify the CM locus for the saturation of an arbitrary immersed slice of a groupoid.

lem-sfb-cm-groupoid-double-restriction vs lem-sfb-cm-groupoid-maximal-slice: the new node has no finite-type point, immersion, affine-existence or dimension assertion. It is the general two-restriction permanence input of 04MX, while the item constructs a maximal slice by finite induction. The source's mention of 04MZ identifies this application, not a restated conclusion.

## Review by Q101

I checked the statements against the sources with the node files open, and checked the citations against the statements themselves rather than their proofs. The three new nodes are self-contained: they specify S and the groupoid, the source and target projections in each restricted groupoid, the saturation maps, the meaning of CM, and all finiteness hypotheses. Their proof arrays and proof dependency lists are empty. Definitions in their statements are cited explicitly; the local flatness explanation is inline. None asserts the full item or merely one of its desired final clauses.

For step 1, `def-sbc-locally-finite-presentation` supplies the affine finite presentation at e(u), and `lem-trf-affine-fibre-point-dimension` explicitly supplies the finite nonnegative local dimension and the tensor-product fibre presentation. Thus the induction parameter is an integer without assuming U or R Noetherian or globally finite type.

For step 2, the finite-type-field-point characterization supplies an affine neighbourhood where u is closed, exactly what is needed to view Spec k(u) as an immersion. The immersion base-change/lft node and permanence node give the locally finite type stabilizer fibre. The groupoid definition gives loops a group structure. The representable-algebraic-space definition retains the actual scheme and identity atlas, and the etale definition supplies lfp for charts. The existing field-groupoid local-dimension statement is applied only to this locally finite type group over k(u), not to an arbitrary groupoid over an arbitrary field extension. The supremum-of-local-dimensions node reconciles its stated dimension convention with the item's chain dimension.

Step 3 spells out the chain comparison for a closed subspace inside an open neighbourhood, and cites the existing open-dimension monotonicity statement for the remaining inequality. Taking the neighbourhood attaining d proves the needed lower bound. This is an elementary argument from the dimension and immersion definitions, not an uncited dimension formula for local rings.

Step 4 checks each part of CM lfp base change separately: affine tensor products from the affine-spectrum fibre-product node, finite presentation after tensoring from the ring permanence node, flatness from the flat-morphism-base-change node, and the fibre formula from the fibre-of-base-change node. The first paragraph of the CM-field-extension statement then applies to locally finite type fibres for any residue-field extension. No finiteness of that field extension and no global Noetherian base is silently added.

Step 5 uses only fibre products and the explicit inverse axiom to identify restricted source and target maps. It writes the source fibre, and identifies stabilizers functorially by loops with the specified object. The cited fibre-of-base-change statement has exactly this field-extension fibre formula. These are short identifications, not a hidden comparison theorem.

Step 6 states strong induction for all inputs and includes the extra projection assertion needed at the next stage. Affine opens exist by the cited basis node. The local presentation A_f = A[z]/(fz-1) verifies lfp for open inclusions. CM survives source-open restriction because the local rings and fibre local rings are unchanged. The open-subspace-local-dimension node supplies the equality of local fibre dimensions. This proves the equality case, including d = 0, rather than merely declaring it trivial.

Step 7 takes exactly the one-dimension drop and CM-at-identity from the new hypersurface statement; it does not read global CM into that statement. The new locus statement applies because s,t are flat lfp and g0 is lfp. It puts b0 in W and makes the whole inverse image CM, which is the global property needed later.

Step 8 uses the affine-open basis to restore affineness after shrinking. Immersion composition is explicitly clause (e) of the existing proper-fp-permanence statement, and lfp composition is the existing lfp-composition statement, not its finite-presentation analogue. The open-local-dimension statement keeps the parameter d-1. The finite-type-point characterization applies to b1 because it is closed in an affine neighbourhood inside the preimage of the open where u is closed. Thus the induction hypothesis is not applied to an arbitrary non-finite-type point.

Step 9 applies the previously stated strong induction, with every hypothesis verified in steps 7--8 and the smaller integer d-1. The restricted stabilizer fibre is G_u by step 5 and the residue-field isomorphism; there is no change of field left requiring a dimension-invariance theorem.

Step 10 cites the new double-restriction statement with the two actual CM lfp saturation maps. The first map need not be surjective onto U. In the source proof, its flat lfp property makes its image open and gives an fppf cover of that image; 04MX then applies. The new statement faithfully includes precisely the hypotheses that make this argument valid. The existing immersion/lft permanence and lfp composition statements give the composite immersion and lfp property.

Step 11 gives the test-scheme description of the twice restricted arrows and forces the intermediate objects, producing the actual isomorphism with direct restriction. The final fibre formula is the same cited base-change formula, now along an isomorphism of residue fields, and its identity is explicitly (c,e(u)). This proves the exact dimension assertion about h^{-1}(u) in the imported statement.

I tested the new statements and induction on the identity groupoid (the locus lemma becomes openness of the CM locus of an arbitrary lfp g), on a group over a field with positive-dimensional stabilizer (d = a, so the equality case does not cut it), and on the pair groupoid of affine space over a field (a = 0 and successive slices lower d to 0). Empty schemes cannot contain the specified finite-type point; empty slices are never produced by the pointed inputs. No reducedness or smoothness of stabilizers is used. The double-restriction input also permits an empty image, when the conclusion is vacuous, and a proper open image, where the fppf argument is over that image. All non-elementary proof steps are below 1000 characters; none exceeds the 2000-character long-step review threshold.

Against delivery-errors B--E: I checked statement-only new files, complete definitions, single TeX escaping, source tags and labels, actual logged searches, blueprint provenance and duplicates (B); each of the 44 citations has a statement quotation and is used only for what that statement says, with short elementary identifications written out (C); the three smaller inputs leave the finite induction, open restriction, hypotheses and final assembly in the item itself, with no back-citation to its parent (D); finite-type points, field extensions, images, fibre products and CM hypotheses were checked as above on the small cases (E). The corrections made during this audit were to avoid unnecessary base-change and immersion-composition nodes, to use the first rather than the Noetherian-base paragraph of the field-extension node, and to make the affine re-shrinking and final residue-field identifications explicit.
