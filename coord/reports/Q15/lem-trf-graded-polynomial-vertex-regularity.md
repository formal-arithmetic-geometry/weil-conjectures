# Stage-1 report: lem-trf-graded-polynomial-vertex-regularity

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-graded-polynomial-vertex-regularity.json`: item, statement; split into five steps. Full item absent from Mathlib; zero new nodes and zero new Mathlib leaves. Reuses two existing Mathlib leaves.
- `citations.json`: seven literal statement quotations, one per step/node pair.
- `searches.jsonl`: actual search-command records; all five current queries are included verbatim in the item in addition to its inherited searches.
- `report.md`: this report.

## Attachments

None. Searched `lean/WeilConjectures/` by the exact blueprint id, vertex regularity, graded-polynomial, monic-direction and linear-substitution terms; no declaration states the item. Existing graded-algebra declarations define the notion but do not give this theorem. No Lean was written or compiled.

## WANTED

None. The full argument is an agent-written refinement, as the imported source explicitly says; it is not attributed as a theorem to Stacks. The supporting monic-regularity passage is available and was read.

## Corrections and scope

The item was unsplit and its sandbox contained only dispatcher marker files. No previous proof/report/search log required recovery. Its statement is correct and unchanged, with unchanged statement dependencies. Its source identifies Stacks Tag 07BV (algebra-lemma-colimit-syntomic), but that tag proves a filtered-colimit theorem; its proof uses monic regularity and does not state the whole graded claim. The delivered proof_origin explicitly remains agent-written. I read algebra.tex around lines 44527–44560 and verified the tag in tags/tags.

I read the chapter and sk-i-curve-zero unit records and the current `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.proof.md`. The latest blueprint uses contracting correspondences and replaces the historical resolution branch identified by this item's inherited provenance. This delivery only resolves its assigned algebraic descendant and changes no chapter/unit route. Blueprint searches for `monic`, `linear substitution`, `homogeneous polynomial`, and `nonzerodivisor` find no equivalent blueprint statement. The ancestor command returns lem-trf-local-term-locality, as recorded. The item's non-unspecified inherited from.place is preserved.

## Unfinished

None for the assigned one-level split. Its only theorem inputs already have status mathlib. No statement dispute, new theorem obligation, attachment, or off-unit unsplit tool is needed.

## Not duplicates

No new nodes. DAG-wide statement/title and tag searches identified lem-trf-infinite-field-top-form-direction and lem-weil-pbc-monic-polynomial-nonzerodivisor, both reused rather than duplicated. The matrix completion, inverse substitution, regrouping of monomials and coefficient calculation are explicit elementary steps, not new nodes or restated clauses.

## Review by Q15

I read the item's source passage (Stacks Tag 07BV, algebra.tex, lemma-colimit-syntomic and its proof) and its parent's delivered proof, where former steps 5–6 were extracted. The source supports monic regularity, while the graded coefficient comparison is written out here. There are no new nodes needing additional sources. I checked B–E of delivery-errors, including the duplicated B–E section, against the actual node and each cited statement.

For step 1, def-pc-standard-graded-algebra states the nonnegative direct-sum grading, B_0=k and multiplicativity, and def-weil-pbc-mv-polynomial-ring gives the finite monomial expansion. Decomposing each coefficient by degree forces b_alpha into B_(n-|alpha|), kills |alpha|>n, and shows exactly why reduction retains only the scalar coefficients with |alpha|=n. This is the crucial coefficient-ring distinction: f need not be homogeneous for the T-degree alone, but H is.

For step 2, I opened lem-trf-infinite-field-top-form-direction and checked its statement gives a nonzero vector with H(v) nonzero for a nonzero homogeneous form over an infinite field with at least one variable. All these hypotheses hold by step 1 and the item. I read the pinned Mathlib MvPolynomial.funext_set in Algebra/MvPolynomial/Funext.lean (57–72), the recorded leaf. Neither a finite field nor a domain assumption on B is introduced.

For step 3, the polynomial definition states both existence and uniqueness of evaluation maps. I avoided an uncited basis-extension theorem: selecting r with v_r nonzero, adjoining the other coordinate vectors, and solving x_1=v_r^(-1)y_r, x_j=y_(i_j)-v_(i_j)v_r^(-1)y_r explicitly proves invertibility. The row-versus-column convention is checked: T_i maps to sum_j M_ij T_j, and the first-column entries are v_i. Composing substitutions with the inverse matrix fixes every generator and coefficient, giving both inverse identities by the cited universal property. Linear forms have total degree one, so the grading is preserved directly.

For step 4, I again used the two definition statements: regrouping finite monomials yields D[T_1], with a written inverse. A term of T-degree below n cannot contribute to T_1^n after linear substitution. A term of T-degree n contributes exactly b_alpha product_i v_i^(alpha_i), with no T_2,...,T_e factors. Summing gives H(v), a scalar, not a coefficient merely congruent to a scalar modulo B_+. The explicit coefficient calculation supplies the conclusion, rather than citing a new node that restates it. Nonzero scalars stay nonzero in B because B_0=k, and in D by constant-polynomial inclusion.

For step 5, I read lem-weil-pbc-monic-polynomial-nonzerodivisor: its statement requires only a commutative coefficient ring and monicity, and concludes q*g=0 implies g=0. D is commutative and q=c^(-1)sigma_M(f) is monic by step 4. I checked the pinned Polynomial.Monic.mem_nonZeroDivisors in Algebra/Polynomial/RingDivision.lean (126–127). The final cancellation uses the inverse substitution and the identity f(g-h)=0 explicitly; no reducedness or flatness of B is assumed. Both theorem citations are Mathlib leaves, so no off-route tool declaration is needed.

I tested e=1: the matrix is (v_1), D=B, and the formula becomes ordinary univariate leading-coefficient normalization. For a ring with zero divisors, take B=k[u]/(u^2), deg u=1, and f=T^2+uT: H=T^2 and v=1 give leading coefficient 1, confirming that the proof does not use B being a domain. A square-zero positive-degree term cannot contribute to T_1^n; this also checks n=1. For e=2 and r=2, the matrix columns (v,e_1) yield precisely the inverse formula written in the proof, confirming the indexing. Positive characteristic causes no difficulty since only scalar inverses are used, not division by n. The item excludes e=0 and H=0, and these exclusions are used at the direction step. No statement correction is required.

All non-elementary uses have cited nodes, and I copied seven verbatim statement excerpts to citations.json and checked substring equality locally. The three elementary steps consist of the stated finite-sum/coordinate computations. Every step is below 2000 characters (maximum 746), and the complete proof text is 2512 characters, so there is no long hidden sublemma. proof_deps is exactly the union of uses. I retained all inherited fields and prior search evidence. I ran the required search command with leanfinder, loogle, grep and leansearch and a second semantic phrasing, read the hits, and found no full-item theorem: homogenization and evaluation declarations do not construct this graded coefficient comparison. No search was invented or service failure recorded as absence.

## Dry-run corrections

The first citation gate found that the excerpt for the standard graded algebra definition was shorter than its required 40 characters. I replaced both excerpts with that definition’s full statement, which also explicitly includes every grading property used in steps 1 and 4. The mathematical argument did not change.

## Continuation verification (2026-10-23)

Resumed the completed sandbox rather than replacing it. The required first dry run on resumption passed at 5d9a9f0f36e. Compared the item with the current read clone: only proof, proof_deps, proof_origin, mathlib_searches, status and split_report differ; the statement and provenance remain unchanged. Re-read all four dependency statements and verified all seven citation quotations against them. Re-read Stacks Tag 07BV (tags/tags:9355; algebra.tex, lemma-colimit-syntomic) and the two recorded Mathlib leaf declarations at their stated lines. Rechecked the explicit inverse matrix, scalar top coefficient and cancellation argument, including the zero-divisor coefficient-ring example already recorded above. The saved five search records were read and reused; their questions and the item statement have not changed, so no search was repeated. Renewed project-source searches found no exact attachment. Rechecked blueprint ancestor and whole-blueprint monic/homogeneous-polynomial searches; there is no equivalent blueprint node. No mathematical repair or additional node was needed.
