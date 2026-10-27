## Worker report

Files written: `dag/nodes/sec-trace-formula/lem-trf-row-minor-ideal-stable-invariance.json` (statement, split; Mathlib has ingredients but no match for this assertion), `citations.json`, and this report. The original statement and its five statement dependencies are unchanged. There are 0 new nodes and 0 new Mathlib leaves. Recorded all five actual search calls in the item in addition to retaining the earlier searches.

Attachments: none. Searched `lean/WeilConjectures/` for the exact blueprint tag, row-minor and minor-ideal terminology, and Fitting ideals. The scalar-left-inverse and depth/minor results concern different assertions and do not attach to this item.

WANTED: none.

The original item was statement-only. No mathematical error was found in it. The source's stabilization argument omits the cutoff case and uses column matrices; the split supplies the cutoff and fixes the row-coordinate convention explicitly. The statement does not assume finite generation of K and the proof never adds it. The blueprint ancestor concerns local terms; the inherited intermediate Fitting-independence branch supplies the precise local source for this tool, rather than a new route for the unit.

Nothing remains unfinished in this one-level split. Dependencies are existing DAG nodes; their own proof completion is separate work.

## Sources and searches

Read Stacks `more-algebra.tex`, Tag 07Z8 (`lemma-fitting-ideal`), the opening kernel description, stabilization paragraph and final invertible-coordinate paragraph, and Tag 07Z7 (`lemma-ideals-generated-by-minors`), especially (2) and (3). Read the current blueprint `main-20261015/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md`, the chapter and unit records, and the existing intermediate Fitting-independence statement. This split realizes the already assigned algebra input below that branch, without making any geometric inference.

DAG searches used the source tags 07Z8 and minor/Cauchy–Binet/block-determinant terminology over all `dag/nodes/`. Blueprint searches were `minor` and `Fitting`; ancestor lookup returns `lem-trf-local-term-locality`. Reused `lem-trf-fitting-ideal-minor-inclusions`, which already states the appended-column and square-right-multiplication inclusions, and the existing Mathlib leaf `lem-weil-pbc-block-triangular-determinant`. No new node was needed.

Mathlib searches were run with msearch.py: LeanFinder on arbitrary submodule determinantal ideals, Loogle `Matrix.det, Ideal.span`, source grep for Fitting/minor-ideal names, LeanSearch on automorphisms/free coordinates, and a second LeanFinder phrasing through presentation independence and adjoining identity blocks. Read the returned signatures: Smith normal form requires a PID, ideals of matrices impose conditions on entries, and matrix representations and Jacobian reindexing do not state this item. None is a one-line specialization giving all three clauses. All calls completed successfully; no unavailable result was called a negative match. The earlier searches remain intact.

## Review by NS

I checked the unchanged statement against Tag 07Z8: K is arbitrary, all matrix row sets are finite individually, the ring is any commutative ring including the zero ring, k is nonnegative, and the convention D=R at ambient rank at most k is preserved. Transposition changes the source's left multiplication into right multiplication; in step 5 the formula C_ij=u(e_i)_j verifies that convention directly. I did not import Schanuel's lemma, which belongs to the parent presentation-independence argument rather than this item.

Step 1 uses the statement of `def-trf-minor-ideal`, which defines the generators by selected rows and columns. Selecting r rows of any finite matrix yields a defining r-row matrix, and a defining r-row matrix itself occurs in the family. This proves equality of generating ideals, not a finite-generation claim. It is elementary and has no uncited multilinearity argument.

Step 2 uses the Leibniz formula actually stated by `def-weil-pbc-matrix-determinant`. When n<=k<n+d, s=n+d-k lies between 1 and d, so all selected rows and columns exist in the added free summand. Their identity matrix has determinant 1 because every nonidentity permutation has an off-diagonal zero factor. If n+d<=k both ideals are R by their definitions. Thus the proof does not accidentally exclude n=0 or k=n.

Step 3 uses `lem-weil-pbc-block-triangular-determinant`, whose statement allows p,q>=0 and an arbitrary lower-left block with upper-right zero. The selected block diagonal matrix satisfies these exact hypotheses with p=r,q=d. Its conclusion gives det(Q)det(I_d); the cited determinant definition gives det(I_d)=1 even for d=0. I read its Mathlib match, `Matrix.det_fromBlocks_zero₁₂`, at `LinearAlgebra/Matrix/Determinant/Basic.lean:726-727`. This is an existing Mathlib leaf, so its different unit is not an off-route theorem requiring a new tool declaration.

Step 4 cites part (2) of `lem-trf-fitting-ideal-minor-inclusions`, whose statement is precisely J_(r+d)(B) contained in J_r(A) for a matrix with d appended columns. Here B has r+d rows, n+d columns, A is its first n columns, and r=n-k>0. Each projected row lies in K by the direct-sum embedding. Step 1 applies regardless of the number of these rows. Thus the citation supplies the needed inclusion directly; no proof hidden inside that node is borrowed.

Step 5 cites part (3) of the same node, which is stated for every square n-by-n C and exactly the entrywise right product AC used here. For each of the finitely many rows in u(K), its inverse under the given automorphism is in K. Linearity computes the product entries. The inclusion applies once to u,K and again to u^{-1},u(K); u^{-1}(u(K))=K gives equality without any determinant-unit assumption or unproved generation theorem. For n<=k equality is definitional.

I checked B1–B10: there are no new nodes to carry duplicate, incomplete-source, or unsupported-Mathlib-leaf errors. C1–C8 are met by the explicit quoted definitions/results and their verified matrix shapes; the only non-elementary inputs are the existing block determinant and minor inclusions. D1–D5 are met because the steps give the actual selected matrices and two directions, rather than new restatement nodes or a circular argument. For E1–E7 I checked the cutoff, n=0, d=0, k=0, the zero ring, K=0, and K=R^n. In particular K=0 gives zero when n>k before and after stabilization, while K=R^n gives R via standard basis minors. Each individual proof step has fewer than 600 characters and hides no long auxiliary argument. Citations.json contains a verbatim statement excerpt for every cited node in every step. No statement correction was required; the corrections to the absent proof are the explicit cutoff case and the row convention.
