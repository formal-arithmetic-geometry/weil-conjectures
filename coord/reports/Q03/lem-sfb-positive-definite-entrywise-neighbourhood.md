## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-positive-definite-entrywise-neighbourhood.json`: item split, with its exact original statement, statement dependencies and blueprint provenance preserved. No new nodes and no new Mathlib leaves.
- `citations.json`: verbatim quotation of the existing eigenbasis leaf used in proof step 2.
- `searches.jsonl`: generated search evidence, retained with its actual results.

## Attachments

None. Searches of `lean/WeilConjectures/` for the item id and blueprint tag, positive definite, `PosDef`, and related names found no project declaration stating this item.

## WANTED

None. The actual non-elementary input is already an existing Mathlib leaf whose source was read locally. The matrix perturbation proof is agent-written; Milne is motivation for its parent only.

## What was wrong and what changed

The live item is an unsplit auxiliary with an empty proof. Its source already correctly says that Milne II §1, Lemma 1.3, printed pp.77–78, does not assert this linear-algebra lemma. I verified those pages (PDF pp.83–84): they concern a positive involution on a finite rational endomorphism algebra. They do not supply the matrix-neighbourhood proof. The exact item statement is true and is unchanged; there is no statement dispute.

The inherited `created` record and long `blueprint.from.via` chain correctly record that the rational-feasibility parent created this auxiliary. I preserved them. The ancestor tool returns None, matching the existing null `from.node`. Current whole-blueprint searches for positive definite and entrywise perturbation found no equivalent node. The chapter/unit records were read; this is below the unit's route and makes no change to that route.

The first local draft unnecessarily created a sphere-minimum node. The first server DAG check found its missing chapter; after that was fixed, the dry run exited with a search-log mismatch and pushed nothing. I then read the existing `lem-sfb-real-symmetric-orthonormal-eigenbasis` leaf and rewrote the proof using it directly. The uncommitted sphere-minimum file was removed from this delivery. Its compactness argument is unnecessary in the final proof. The final delivery changes only the item and its report.

## What could not be finished

Nothing remains in this stage-1 item. No Lean was written or compiled. The independent maintainer review remains the next project step after delivery.

## Not duplicates

No new node is created. I searched the whole DAG for positive definite, symmetric matrix, perturbation, and orthonormal eigenbasis, and read the existing rational-feasibility parent, split-real sum-of-squares parent and spectral leaf. The spectral leaf asserts an eigenbasis and is reused; the rational-feasibility parent asserts a rational solution to exact rational equations and calls this item's perturbation neighbourhood. Neither duplicates this item.

## Review by Q03

I read `coord/brief-stage1.md`, the stage-1 contract, the three blueprint levels in SETUP, GOAL, the chapter/unit records and delivery-errors B–E. For the mathematics I read the full item statement, the parent's uses of it in steps 3 and 5, the full statement of `lem-sfb-real-symmetric-orthonormal-eigenbasis`, Milne printed pp.77–78, and the pinned Mathlib `Analysis/InnerProductSpace/Spectrum.lean`: real eigenvalues at 279–281, eigenvectorBasis at 300–304, and apply_eigenvectorBasis at 325–327. The leaf really provides an orthonormal eigenbasis for every finite-dimensional real symmetric linear operator. It is a Mathlib tool and is in this item's own unit.

Step 1 has no citation: for n=0 there are no nonzero vectors, so epsilon 1 meets every clause. It removes the empty case before taking a minimum or dividing by n.

Step 2 cites only the spectral leaf. All its hypotheses are verified: R^n has its coordinate basis; the dot product is symmetric bilinear and its sum of squares is positive for nonzero vectors; T is a real linear map given by multiplication by G. Exchanging the two finite indices and using G_ab=G_ba proves exactly the symmetry equation the leaf assumes. Its statement supplies precisely the real eigenvalues and orthonormal basis quoted in `citations.json`; I do not take a lower bound or positivity of eigenvalues from its proof.

Step 3 is elementary from that basis and the item's strict positivity hypothesis. Each e_i has norm square 1, so it is nonzero, and q_G(e_i)=lambda_i>0. The minimum of a finite nonempty list of positive reals is positive. If z=sum t_i e_i, expanding both inner products term by term gives q_G(z)=sum lambda_i t_i^2 and sum z_a^2=sum t_i^2. Thus q_G(z)>=c sum z_a^2. This uses neither compactness nor an uncited coercivity theorem.

Step 4 is an explicit finite-sum computation: n S-L^2 equals one half of sum_ab (|z_a|-|z_b|)^2, so it is nonnegative. Triangle inequality and the entrywise bound give |q_(H-G)(z)| <= epsilon L^2 <= epsilon n S. With epsilon=c/(2n), q_H(z)>=c S/2; a nonzero vector has S>0. This proves every required H positive definite while keeping its assumed symmetry. No additional non-elementary result is used, and all proof steps are below 2000 characters.

I checked n=0 separately, n=1 (G=[g], g>0, epsilon=g/2), scalar matrices with arbitrarily small positive scalar, unequal positive eigenvalues, and off-diagonal perturbations. In particular G=I_2 with H having off-diagonal entries t gives q_H(1,-1)=2-2t, consistent with the conservative epsilon=1/4. Semidefinite G=0 would fail, which confirms why strict positive definiteness, rather than nonnegativity, is necessary. Repeated eigenvalues cause no problem; only their finite positive minimum is used. Symmetry of H is retained.

I read the actual Mathlib search hits. Matrix.PosDef and its comparisons with quadratic forms and strict positivity state definitions or equivalences; IsOpen.matrix concerns independent membership of entries in one open scalar set, so it does not state openness of positive definiteness. I read those candidate sources. A second semantic phrasing and focused source greps were run by msearch.py and recorded as generated in searches.jsonl. Original search records remain intact and new records reproduce the log. No unsupported Mathlib match is claimed. B1–B9 are vacuous for new nodes; C1/C4 are satisfied by the one checked citation and the fully written finite computations. No statement or source correction is hidden.
