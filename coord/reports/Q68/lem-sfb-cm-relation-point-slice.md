# Worker report

Files written:
- dag/nodes/sec-six-functors-basics/lem-sfb-cm-relation-point-slice.json: split statement, five proof steps; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-cm-groupoid-maximal-slice.json: new statement-only lemma, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-groupoid-quasifinite-locus-descent.json: new statement-only lemma, unsplit; no Mathlib match.
- citations.json: verbatim statement quotations for every step/dependency pair.

Attachments: none. Searched the project by the blueprint tag and by Cohen--Macaulay/groupoid/slice terminology. The existing CohenMacaulayFlatQuasiFiniteChart and fibre-dimension files concern one morphism and do not give this relation slice.

WANTED: none.

The statement is retained mathematically; doubled TeX backslashes were normalized. The imported node had no proof. In particular, ordinary openness of the quasi-finite locus alone does not permit shrinking B so that the entire saturation has the property: the groupoid descent input 04LH/047W(2) is necessary. Also the open W in Stacks' proof need not be affine; the final principal-open shrink restores the affine conclusion. No hypotheses are added and no clause is removed.

Unfinished: the two new inputs are intentionally left statement-only, as required by a one-level stage-1 split. Their future splits should follow the complete proofs in 04MZ and 04LH/047W(2), respectively. The maximal-slice argument uses induction on finite fibre dimension, one-equation slicing (more-groupoids lemma-slice), CM-locus descent, and double restriction. The locus argument compares the two pullbacks along the groupoid composition diagram; the common quasi-finite locus is pulled back from its inverse image under the unit section. These are source arguments for future work, not proofs placed in the unsplit statements.

## Not duplicates

lem-sfb-cm-groupoid-maximal-slice vs lem-sfb-cm-relation-point-slice: 04MY is shared setup only. The new node is 04MZ for arbitrary scheme groupoids, allowing positive-dimensional stabilizers; it gives a CM saturation and equality of fibre and stabilizer dimensions, without a quasi-finiteness conclusion. The item uses trivial stabilizers and then a separate quasi-finite-locus descent to get its conclusion.

lem-sfb-cm-groupoid-maximal-slice vs lem-sfb-fppf-space-relation-slicing: the existing node concerns a global replacement of a flat equivalence relation with the same fppf quotient; the new node concerns one finite type point of a CM groupoid with arbitrary stabilizers and makes no quotient assertion.

lem-sfb-cm-groupoid-maximal-slice vs lem-sfb-field-groupoid-stabilizer-dimension: the existing node assumes the object space is the spectrum of a field and compares global dimensions of the arrow and stabilizer spaces. It constructs no slice of a groupoid over an arbitrary object scheme.

lem-sfb-cm-groupoid-maximal-slice vs lem-trf-cm-closed-point-flat-quasifinite-slice: the existing node slices the source of a single flat morphism. Here the slice must be in the object scheme and control its entire saturation by a groupoid, which the single-morphism lemma does not assert.

lem-sfb-groupoid-quasifinite-locus-descent vs lem-sc-quasi-finite-points-open: the existing result gives an open in the source H of h. The new result proves that this entire open is p^{-1}(W) for an open W of B; this requires the groupoid symmetry.

lem-sfb-groupoid-quasifinite-locus-descent vs lem-sfb-stack-unramified-locus-base-change: that existing result is an unramified locus on algebraic stacks with smooth charts; the new statement is the locally quasi-finite locus of a scheme-groupoid saturation with merely locally finite type projections and g.

DAG tag searches for 04MZ, 04LH and 047W found no existing statement giving either new lemma. Whole-blueprint searches for slice, groupoid, maximal slice, quasi-finite locus, Cohen and stabilizer found no equivalent blueprint node. Searched the project before creation and read the Mathlib hits: scheme smooth charts and quasiFiniteLocus (ZariskisMainTheorem.lean:316--322) do not give either groupoid theorem. Searches were run only through msearch.py and are recorded verbatim, including the second semantic phrasing of each node. No unavailable service was treated as a negative result.

## Review by Q68

I read Stacks more-groupoids.tex, Situation 04MY and the statements and proofs of 04MZ and 04N0, together with 04LH and Remark 047W, especially item (2). For the affine conversion I read morphisms.tex 0397, lemma-locally-quasi-finite-rel-dimension-0, and compared the existing ring-criterion statement. I read the latest blueprint direct-images proof (3) and its unit statement: this is a subsidiary bootstrap input on the already recorded branch, not a replacement of that unit's proof. No SGA source is used.

Step 1 uses the full Yoneda bijection in lem-pc-yoneda, not merely faithfulness. Applying it to the natural identity, reversal and composition operations on the relation gives actual scheme morphisms over S. Uniqueness of an arrow with given endpoints proves the equations and proves G is V scheme-theoretically, on every test scheme, not just on geometric points. def-a1-groupoid-scheme defines precisely these operations; def-pc-fibre-product supplies their domains. def-weil-affine-spectrum explicitly says the spectrum of a field has one point, so its dimension is zero. These are elementary constructions from the cited statements.

Step 2 uses the new maximal-slice node's exact clauses: affine B, lfp immersion g_0, the point b with unchanged residue field, CM and lfp h_0, and the fibre dimension equality. Its statement is a direct subset of 04MZ with the identification in 04MY written out. Because the immersion preserves the residue field, the restricted source fibre in 04MZ is exactly the fibre h_0^{-1}(v). CM implies flatness by the definition explicitly included in the new node. It does not assume G is quasi-finite and does not assert the item's final clause.

Step 3 uses the finite affine presentations in def-sbc-locally-finite-presentation, the explicit tensor-product fibre identification in lem-weil-pbc-fibre-product-affine-spectra, the equivalence in lem-weil-pbc-ring-quasifinite-zero-fibre-dimension, and the affine-neighbourhood definition in pqf-def-quasifinite. I checked that the ring map is finite type and that the prime in its fibre is the point x. Local topological dimension is unchanged on an open containing x because its neighbourhood system is cofinal. Thus the ring criterion applies without a global Noetherian hypothesis. The ring criterion is declared as a generic off-unit tool use, with the affine computation.

Step 4 uses the locus-descent node, which is exactly 04LH with Q=R=locally finite type and P=locally quasi-finite, a valid specialization explicitly listed in 047W(2). Both groupoid projections and g_0 are lft because their finite presentations have finitely many generators. The lemma states equality of the entire quasi-finite locus with p^{-1}(W), and its identity-point clause proves b lies in W. There is no unsupported inference from a single quasi-finite point to an entire fibre.

Step 5 writes the principal-open ring C_f=C[z]/(fz-1), so its lfp assertion and that of restricted h_0 are checked directly on finite presentations; lfp composition is exactly the statement of lem-sbc-locally-finite-presentation-composition. The fibre-product universal property identifies the open p^{-1}(A), and flatness is unchanged on those stalks by def-weil-flat-morphism. The last cited restriction lemma really allows an arbitrary open source, with no quasi-compactness condition, so it supplies the remaining property. No new lemma is hidden in this elementary restriction step. All steps have fewer than 2000 characters.

I checked small cases of the new statements. For the identity groupoid on any scheme, an affine neighbourhood gives a maximal slice of fibre dimension zero; in the locus statement H=B and h=g, so W is just the ordinary quasi-finite locus. For a group scheme over Spec k the maximal-slice dimension equality retains the positive stabilizer dimension (so this is not a disguised quasi-finite-slice assertion). For an empty B the locus statement is vacuous; the maximal-slice lemma has a named point and hence makes no existence claim for an empty U. Nilpotent schemes cause no issue: stabilizer triviality is on all test schemes, and the source theorem allows nonreduced fibres.

I checked B--E: new statements introduce all objects and notions, have no proof or proof dependencies, and have sources by verified Stacks tags and labels. The item's assembly carries the trivial-stabilizer argument, dimension-to-quasi-finiteness conversion, whole-locus descent and final affine restriction. Neither new node restates the item or just one of its clauses. Every proof citation was opened and its statement copied verbatim into citations.json. The three non-leaf off-unit tools are declared in split_report.tool_uses. No target statement, chapter or unit was edited, and no Lean file, compiler or Lake tool was used.
