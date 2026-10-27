# Stage-1 report

## Files written

- dag/nodes/sec-trace-formula/lem-trf-lattice-monoid-minimal-determinant-tuple.json — existing statement, now split; no exact Mathlib match.
- citations.json — three full, verbatim statement quotations for the three proof citations.
- report.md and searches.jsonl — report and actual search-command records.

No new nodes and no new Mathlib leaves. The item keeps its statement, statement dependencies, source, creation record, and blueprint ancestry. Its three proof steps total 1743 characters.

## Attachments

None. Searches for the exact blueprint tag and for minimal/least determinants in lean/WeilConjectures found no declaration stating this item. Matrix.cauchy_binet is an existing closed dependency, not an attachment for the item. Matrix.exists_strictMono_submatrix_det_ne_zero_of_mulVec_injective covers an injective matrix over a field and does not minimize over monoid tuples.

## Literature wanted

None.

## Findings

The item is true as stated. Root saturation is unnecessary and has not been added. The nonnegative-generation assumption is stronger than this proof needs; it remains unchanged. The group-spanning condition supplies the integer right inverse directly, so no field extension, abstract basis-selection lemma, or new nonsingular-minor node is needed. A bare assertion of full rank would have concealed this construction.

Read Stacks algebra.tex lines 282–288, with Tag 0F0K verified in tags/tags as algebra-item-cauchy-binet. It supplies exactly the rectangular determinant identity, not the monoid or minimizing assertion. The application and minimum assembly are therefore explicitly agent-written. Read the current chapter and unit records and the latest blueprint statement and proof of lem-trf-local-term-locality. The latter now follows the contracting-correspondence route; this lattice node is the historical auxiliary descendant recorded in its inherited blueprint ancestry, not a replacement of the current unit proof. No source from SGA is used.

## Searches and reuse

The sandbox initially contained no node or report. Retained all inherited searches from the live node. Ran fresh leanfinder, loogle, grep and leansearch searches through msearch.py, including a second semantic phrasing, and read the results. Both semantic services answered. No combined theorem gives the item or a one-line specialization. Read the subgroup-index formulas at CardQuotient.lean:85–103: they assume a basis already supplied. Read Matrix/BaseChange.lean:27–65 and Echelon/Pivot.lean:145–162: their hypotheses concern subfields or supplied pivot data. The other returned lattice norm bounds, fundamental domains, fixed-determinant representatives, generating-set minimality and kernel bounds do not minimize tuple determinants in a prescribed monoid.

Searched the whole DAG by statement concepts, Cauchy–Binet/0F0K, well-ordering, least elements and Nat.find, and the blueprint with blueprint_refs.py searches for Cauchy, determinant, least and minimum. Found and reused lem-weil-pbc-cauchy-binet and the more general Mathlib leaf lem-kun-extended-naturals-minimum. These are generic tools outside the item unit, declared in split_report.tool_uses; neither replaces a geometric route step. Definition def-weil-pbc-matrix-determinant is the unchanged statement dependency.

## Not duplicates

No new nodes. In particular, no new monoid-minor lemma restates the first clause of this item, and no new natural-number minimum lemma duplicates lem-kun-extended-naturals-minimum.

## Review by NN

I checked the split against delivery-errors B through E with the item and the actual cited statements open. The source for the item is Stacks 0F0K, read above; there are no new nodes needing sources. The item's complete statement introduces the monoid and finite generators and defines its absolute determinant. No statement dispute or correction is needed.

Step 1 is an elementary entrywise construction from the group-spanning hypothesis: for each of the r standard coordinate vectors choose its m integer coefficients, and put these into an m by r matrix C. B is r by m, so BC is r by r, with precisely the coordinate entries of the identity. No monoid subtraction or nonnegative coefficient claim is used.

Step 2 cites the statement of lem-weil-pbc-cauchy-binet, which explicitly allows rectangular matrices over any commutative ring, permits an empty sum when m<r, and enumerates the matching column and row minors in increasing index order. Thus it applies over the integers to B,C without assuming m>=r. The other citation is def-weil-pbc-matrix-determinant: its actual Leibniz formula, not merely a name, computes the identity determinant as 1. If all generator minors were zero every product in that finite sum would vanish; hence a nonzero minor exists and its increasing column enumeration is the required first tuple in S. The zero-size and empty-index conventions cannot invalidate this step: r>=1, and m<r would force the displayed contradiction.

Step 3 cites lem-kun-extended-naturals-minimum. Its statement actually gives a least element of every nonempty subset of {-infinity,0,1,...,infinity}, not just an abstract infimum. The set D contains only finite positive natural numbers, is nonempty by step 2, and is included with its ordinary order unchanged. Membership of the attained minimum therefore gives an actual tuple v in S^r. Comparing with every member of D proves precisely the quantified conclusion, including all ordered tuples, not merely generator subtuples. All three citation quotes copy complete statements verbatim; no step relies on a cited node's proof.

Small cases: for r=1 and S generated by 2 and 3, the group span is Z but S contains no 1; the minimum is 2, so neither the statement nor the proof accidentally claims a basis or determinant 1. Here B=(2,3), C=(-1,1)^t gives BC=1. For S=-N, the determinant may be negative and the absolute-value formulation gives minimum 1. For S=N^r the standard tuple has minimum 1. Zero or repeated generators cause no difficulty since only one nonzero minor is needed. For m<r, including m=0, group-spanning and Cauchy–Binet are incompatible; the proof does not assume away this case. r=0 is excluded by the item, although the empty tuple would also have determinant 1. No saturation, positivity of generator coordinates, or characteristic assumption beyond working in Z is imported.

The non-elementary steps are each below 700 characters and expose exactly their two tool applications. No long step hides a separate comparison or standard lemma. Dependencies equal the union of step citations; all cited ids exist and are unmerged. No cited node depends on this newly created lattice task. I checked that the unchanged notions are either defined inline or covered by the determinant definition dependency. There is no hollow construction, circular appeal, moved-out clause, false edge case or silently weakened statement.

## Unfinished work

None for this stage-1 split. Server preflight and delivery are run after writing this report; their command output records the validation and pushed commit.
