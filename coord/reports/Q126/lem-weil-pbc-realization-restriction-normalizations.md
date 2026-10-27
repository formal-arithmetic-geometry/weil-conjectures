# Stage-1 report: lem-weil-pbc-realization-restriction-normalizations

## Files written

- dag/nodes/sec-proper-base-change/lem-weil-pbc-realization-restriction-normalizations.json: statement node, split into four proof steps; no Mathlib match.
- citations.json: ten verbatim quotations, one for every step/node pair.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. The existing searches are retained; searches performed for this item are recorded in searches.jsonl and appended to mathlib_searches when their tool/query pair was not already present.

## Attachments

None. Searched lean/WeilConjectures for the blueprint id, restriction/realization normalizations, and realization scalar/pull/push names. The hits were unrelated normalizations, not a project declaration giving every clause. No Lean file was written and no compiler was invoked.

## WANTED

None. The relevant PDF, Stacks source, and current blueprint proof are available.

## Findings and changes

The item arrived unsplit, without a repair note or existing sandbox node. Its statement has been retained exactly. Its source is context rather than a printed proof of these three formulas: Remark 6.8.15 gives the ambient operations and adjunction, and Lemma 6.8.2 gives the coefficient localization. The explicit normalization argument is marked agent-written. I read those two PDF passages, Stacks sites-cohomology.tex labels lemma-derived-pullback-composition (0D6D), lemma-derived-pushforward-composition (0D6E), and lemma-adjoint (07A6), and main-20261015's thm-weil-pbc-finite-extension.proof.md. No SGA source is used.

The completed-pull and localized-push nodes already supply the actual comparisons and their normalizations. The ring-sheaf-change node already states the full ambient Hom formula. Therefore creating new nodes for the three equations would merely relabel clauses of this item (D1). The proof instead performs the cancellation, scalar-adjunction substitution, and counit substitution explicitly. No new lemma is hidden in a long step: the four step lengths are 627, 1052, 646, and 730 characters.

The item is auxiliary to the finite-extension blueprint's integral-to-rational step through the recorded realization ancestry. It is not the unit key node, and no chapter or unit record needs changing. All cited statements belong to the item's own unit; no off-route tool use is proposed.

## Not duplicates

No new nodes. Whole-blueprint searches for scalar comparison, coefficient change, restriction, and localization, and DAG searches for scalar units and restriction transposes, found existing tools that suffice. In particular the coefficient-square and ring-sheaf-change results are reused, rather than restated. Blueprint matches about condensed coefficient changes do not state this item's actual ordinary coefficient comparisons; same_as remains empty.

## Unfinished work

None for this one-level split. Downstream nodes keep their existing states. This report makes no claim to have formalized the proof in Lean.

## Review by Q126

I checked the split against delivery-errors B through E, reading the cited node statements rather than treating their proof bodies or their names as interfaces. There are no new nodes requiring independent small-case tests or source assignments. The original statement's objects and all ten statement dependencies remain unchanged.

Step 1 uses realization-completed-pull for the actual integral coefficient map and the localized continuous map. Its statement explicitly identifies precomposition and the chosen localization comparison, so this is not an arbitrary replacement of coefficient isomorphisms. Realization-coefficient-square gives equality of the two composites for exactly the normalized scalar presentations. The schemes satisfy its Noetherian, finite-dimensional and invertible-ell hypotheses. Ring-sheaf-change-adjunction then applies with R=A, S=E on the small pro-etale sites and gives ambient b,d. Its stated compatibility will be used in step 4. This is the only non-elementary assembly step; all theorems it applies are cited.

Step 2 uses realization-completed-pull's displayed factorization alpha_comp = a F(gamma^-1). Cancellation with F(gamma) identifies the alpha^o in this item with that same ordinary a, rather than a merely isomorphic comparison. Continuous-coefficients-immersion-restriction supplies E_W = A_W[1/varpi] as sheafified localization on Noetherian schemes; I do not extend its immersion pullback clause to arbitrary h. The arbitrary h coefficient isomorphism instead comes from realization-completed-pull. Realization-scalar-functor identifies the unit as the derived map m -> 1 tensor m. Localization-inverse-image-coherence states both unit preservation on unbounded derived categories and compatibility with a specified coefficient-ring identification. Written with b, its equation is b r(a) j = P(j), so cancellation gives the desired formula with the correct direction of b inverse. Thus the step is a short substitution in cited equalities, marked elementary; it does not prove a new comparison lemma inline.

Step 3 reads the normalization sentence of realization-localized-push literally: beta is the extension/restriction transpose of Q(j), using the specified coefficient-restriction comparison. The map has target r_U Q^E F_T M, so d inverse, not d, follows Q(j). Realization-scalar-functor supplies F_U left adjoint to r_U. The defining Hom formula sends beta to r_U(beta) followed on the right by j_{U,QM}, proving the equation. Nothing here uses the parent realization-adjoint-comparisons node or assumes that beta is already the horizontal mate; this avoids circularity.

Step 4 uses ring-sheaf-change-adjunction's complete Hom formula. For its variables M=Q^E Z, N=Z, t=epsilon^E_Z, the adjunct is the identity by the definition of counit. The formula then gives d_Z as the A-adjunct of the left side in our item. Applying the inverse adjunction sends d_Z to epsilon_{r_T Z} P(d_Z). Both sides have domain P r_U Q^E Z and codomain r_T Z. In particular its ambient quantified N permits every E_T-complex Z. I verified that no step claims r_T Z belongs to the bounded integral category.

I checked h=id, zero objects, the empty scheme, E=Q_ell, and ramified finite E. The identities reduce respectively to the scalar unit identity, zero morphisms, identities in the trivial module category, or the same localization-unit equation; none requires a normalization of varpi to ell. For M or N killed by a power of varpi, its scalar extension is zero, so the unit-transpose equations have zero target and remain valid. I also checked an unbounded ambient Z: step 4 invokes an unbounded ambient theorem and has no constructibility or boundedness premise. Fraction denominators in step 2 are unchanged by the cited inverse-image/localization theorem.

The citations file quotes were verified as literal substrings of each cited statement. The source checks above also distinguish the ambient ordinary operations from completed pullback: the only passage between them is the actual gamma and its inverse. This corrects the potential gap of identifying alpha^o with an unspecified pullback isomorphism. Mathlib searches used all four required tools and a second semantic phrasing. I read PushforwardContinuous.lean 260-305, PullbackFree.lean 60-104, and ChangeOfRings.lean 905-916: these give underived sheaf adjunctions or ordinary module scalar units, not this coefficient-specific derived theorem. No unavailable service was recorded as no match.
