## Files written

- dag/nodes/sec-smooth-purity/lem-pur-kummer-product-shear-homotopy.json: statement node, now split, not in Mathlib; statement unchanged.
- citations.json: nine verbatim statement excerpts, one for each step/dependency pair.
- report.md: worker report and direct-delivery self-review.

No new nodes and no Mathlib leaves. Existing search records are retained, and five searches actually run with the required msearch.py command in this sandbox are appended to the item's mathlib_searches. searches.jsonl is the unmodified search-command log.

## Attachments

None. I searched all lean/WeilConjectures for the blueprint id, shear, frame independence, and Kummer product terminology. I read FrameIndependence.lean, especially AlgebraicGeometry.Etale.restrictSupportedClass_kummerBoundaryProduct_mulVec at line 391 and its hypotheses at lines 222-224. That theorem supplies an etale supported-class equality under a normalized HasKummerClass datum. It does not state this item's explicit interpolating class, its two endpoint identities and the equality of the two pro-etale section pullbacks with the concrete arbitrary-index coefficient construction. It is therefore not an attachment of every clause of this item. I did not infer completion from the fact that this nearby theorem's own proof has no sorry.

## WANTED

None. The source needed for this split is available locally.

## Corrections and source issues

The imported item was statement-only. I supplied its argument without changing its statement, coefficient range, or hypotheses. Its source is the current main-20261015 lem-pur-frame-independence.proof.md, paragraph "Elementary shears", read in full together with the smooth-purity chapter record and sk-prop-a1-kummer unit record. The parent source's assertion that a relevant cohomology sheaf is constant is not established by the supported Kunneth statement, which also assumes separated finite-type schemes. This was already repaired in the existing lem-pur-supported-affine-line-homotopy. I reuse that precise arbitrary-base theorem rather than repeat the unjustified inference; no new route or statement dispute is introduced. In particular the tuple on A^1_X is used only as a tuple of functions, not claimed to be an etale frame neighborhood.

The unit's affine-line route is retained. Definitions from other units are notions. The coefficient lemma lem-pur-twist-sheaf-locally-free is filed in sk-def-sf-admissible: it is declared in split_report.tool_uses for the locally free finite-twist input to Step 2. The other statement-valued tools are in sk-prop-a1-kummer. This coefficient flatness fact does not replace the unit route. There are no SGA citations.

## Unfinished work

None for this one-level split. The pre-existing dependencies keep their existing status and proofs. No Lean was written and no compiler, Lake or build command was run.

## Not duplicates

No new nodes. Whole-DAG and imported-blueprint searches for shear and affine-line homotopy were checked; the broader existing supported affine-line theorem is cited, not recreated. The elementary ideal computations and endpoint substitutions remain proof steps.

## Review by NP

I read the item's current source paragraph and the full statements of every cited node. I also read def-pur-support-cohomology, the coefficient conventions and the relevant existing supported-homotopy proof. This is a direct-delivery self-review, not a claim of a second independent reader.

Step 1 uses only the affine-chart presentation in def-sbc-affine-space. The two explicit expressions h'_i=h_i+ah_j and h_i=h'_i-ah_j prove equality of the ideals in both directions. The same subtraction in R[t] proves equality to IR[t], and the displayed tensor quotient identifies the fibre product as a closed subscheme, not merely as a set. The fact i and j are distinct is essential because it keeps h_j among the unchanged generators. No invertibility of a is assumed.

Step 2 uses the arbitrary-unit clause of def-pur-frame-class, not the definition's smooth-frame hypothesis. The individual functions are units on precisely their own complements. thm-pur-with-support-exactness explicitly includes the small pro-etale finite-torsion case and gives the degree-1 to degree-2 connecting map for each pair. def-pur-supported-cup gives the operation on arbitrary k-schemes with intersected support and summed degrees. lem-pur-twist-sheaf-locally-free(3) supplies the finite locally free rank-one A(1); def-coefficient-twists-detailed explicitly defines positive twists by its tensor powers. Since ell is invertible on every k-scheme in the conventions, that lemma applies, and no divisibility of n by the ramification index is used. The induction on the number of factors checks the support, degree and coefficient of eta. The c=0 convention is retained, although the shear assertion itself assumes c>=2.

Step 3 uses the polynomial presentation of def-sbc-affine-space and evaluates at t=0 and t=1. Each individual principal ideal and each complementary open is pulled back explicitly, as is the total ideal IR[t]. This checks the supports on which Step 4's maps are defined. The argument is affine-local and does not assume X is affine or separated.

Step 4 cites lem-pur-supported-cup-functoriality. Its statement explicitly supplies Kummer pullback, compatibility with localization boundaries, cup-product pullback, the pro-etale case, and arbitrary scheme morphisms. I checked all those clauses, which are included in its verbatim citation excerpt. It applies to the restriction of each section to each individual complement. The written induction on the ordered product avoids any use of permutation symmetry, so there is no hidden sign or twist-symmetry assertion. Pullback of the individual support intersections agrees with Step 3's total support.

Step 5 uses exactly the section-inverse clause in lem-pur-supported-affine-line-homotopy with q=2c, r=c and C=C_h. I checked that its statement has arbitrary k-schemes, arbitrary closed subschemes, every n>=1, and pro-etale finite twists. In particular it adds no smoothness, connectedness, finite-type or strictly local hypothesis. It says that both s_0^* and s_1^* invert the same canonical p^*, so equality applies to this specific eta. The final equality and the specialization to an etale frame neighborhood now follow from the two endpoint identities.

I tested c=2 with either order of i,j, a=0, a nilpotent, h_j=0, an entry equal to a unit (empty total support), the all-zero tuple (full total support), nonreduced X, and empty X. The algebraic identities still hold in arbitrary commutative rings; the localization, cups and homotopy tools impose no regularity assumption in any of these cases. For c=0 or 1 there are no two distinct indices, so no shear assertion is required. All five proof steps are shorter than 2000 characters, and none hides a further lemma. All non-elementary inputs are cited statements, no new node restates a clause, and every citation excerpt was checked as an exact substring of the cited statement. Statement dependencies are unchanged because the statement is unchanged.
