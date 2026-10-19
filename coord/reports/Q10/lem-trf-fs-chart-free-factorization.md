# Q10 stage-1 report: lem-trf-fs-chart-free-factorization

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-fs-chart-free-factorization.json`: statement, split; nine proof steps; statement unchanged; fresh Mathlib search records appended while retaining all inherited search records and provenance.
- New nodes: none. New Mathlib leaves: none. The existing finite torsion-free group basis, determinant definition and adjugate identity are Mathlib leaves; the existing general Cauchy–Binet node is reused as a tool.
- `citations.json`: one verbatim statement quotation for every node used by every numbered proof step.
- `report.md`: this report. `searches.jsonl` is the genuine msearch.py log. `scratch/` contains the source extraction and the local writing script, not delivery nodes.

There was no previous item copy or report in the sandbox, only dispatcher brief files. I copied the current repository node, retained its statement, source, inherited searches, created record and blueprint ancestry, and supplied its missing proof.

## Attachments

None. Searches of the read-only slopmaster2 and master project sources by the exact id, chart factorization, saturated monoid, group completion and cokernel/basis terminology found no project declaration giving this item. The exact node id is also absent from the upstream-name index. The log/toric chart notions used here are not formalized by a project theorem with these clauses. Abstract Grothendieck-group declarations do not lift a basis into Q, and sorry declarations in master would not qualify in any event.

## WANTED

None. The source material and elementary arithmetic needed for this algebraic refinement are present.

## What was missing and what changed

The item had an empty proof and explicitly called its general chart factorization an agent-supplied refinement of ILO VI Proposition 1.9. I read that proposition and its proof, printed pp. 70–71: it constructs a particular nodal monoid pushout and says that its chart map is injective with group cokernel Z. It does not assert the general basis-lifting claim as a theorem. I therefore preserved that distinction and marked the new proof as agent-written, with the precise source ingredients stated. I also read ILO VIII 3.1.1–3.1.2 (localization and sharpening), VIII 3.1.17 (saturation), and VI 3.7(a) (finite torsion-free group basis), rather than attributing the new minimal-determinant argument to those paragraphs.

The key extra argument is that S = image(Q -> Q^gp/g(P^gp)) is saturated. It is important here that the kernel subgroup comes from elements of Q: for nx=q+g(a)-g(b), the identity n(x+g(b))=q+g(a)+(n-1)g(b) puts the right hand side in Q. This allows saturation of Q to apply. No assumption that g(P) is a face, and no torsion-freeness of Q^gp, has been inserted.

The finite free group theorem alone does not give basis vectors in S. The proof chooses a tuple from S of least positive absolute determinant. If it fails to span the integer lattice, an integer vector outside its span has rational coordinates in that tuple. Subtracting the floors produces an integer vector with coordinates in [0,1), not all zero. Clearing their finite denominators and using saturation puts that vector in S. A column replacement then contradicts the minimal determinant. The final steps lift these basis vectors to Q and explicitly check the kernel, surjectivity, restriction to the monoid and identification of the induced group map.

The current blueprint's sk-i-curve-zero unit and lem-trf-local-term-locality proof follow the contracting-correspondence/normal-cone route. This node belongs to an already recorded historical nodal-chart ancestry. I did not change the chapter, unit, ancestor, or that route, and make no new unit-realization claim.

## Mathlib and duplicate searches

Before creating any auxiliary node I searched the whole DAG and blueprint for the full item, saturated monoids, lattice bases, fundamental parallelepipeds, integer matrices, determinant descent, column replacement, Cauchy–Binet, and the determinant declaration names; I also searched project Lean sources. Blueprint_refs ancestor returns lem-trf-local-term-locality. Blueprint search found no equivalent blueprint statement; same_as stays [].

All fresh Mathlib requests were run through the required msearch.py command and their exact queries and machine summaries are in searches.jsonl. Two semantic phrasings of the item returned only abstract group completions, unconstrained bases and monoid quotient maps, not this factorization. These searches are appended to the item's inherited records. Loogle's unquoted GrothendieckAddGroup identifier was unknown to that service; I report the error and do not treat that result as evidence of absence. The second semantic phrasing found Module.basisOfFiniteTypeTorsionFree', which is exactly the existing lem-trf-fg-torsionfree-group-free and is reused.

I investigated whether the rational-coordinate rounding/determinant descent needed an unsplit lattice lemma. Searches returned ZSpan.fract_mem_fundamentalDomain, ZSpan.floor and related fundamental-domain results; I read Mathlib/Algebra/Module/ZLattice/Basic.lean lines 90–195. They do not by themselves assert this monoid-constrained basis result. The requisite floor calculation is only the explicit identities in Step 5 after applying the already existing adjugate node, so no lattice node was created.

Further logged semantic searches and a quoted Loogle query found Matrix.det_updateCol_sum; the required grep located it at Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:435, and I read its statement and proof at lines 432–439. It states det(A with column j replaced by sum c_i A_i)=c_j det A. However it is also two lines from the existing Cauchy–Binet statement: the replacement matrix is AE for an identity matrix E with column j replaced by c, the square case gives det(AE)=det A det E, and the defining permutation sum gives det E=c_j. Under the brief's no-new-elementary-node rule I wrote that calculation in Step 6 and created no determinant node. The non-square Cauchy–Binet statement is also exactly what Step 3 needs to extract a nonsingular tuple from generators spanning the group. Its literal source is Stacks Tag 0F0K, algebra-item-cauchy-binet; I read that item in algebra.tex. I read the adjugate calculation in Stacks Tag 07DQ, algebra-lemma-matrix-left-inverse, and the entire statements of the existing determinant, adjugate and group-basis nodes.

## Not duplicates

No new nodes are delivered. In particular, I did not duplicate lem-trf-fg-torsionfree-group-free, lem-weil-pbc-cauchy-binet, lem-weil-pbc-matrix-adjugate-identity, def-weil-pbc-matrix-determinant, or def-weil-matrix. The existing Gordan lemma gives finiteness of cone lattice points, not a basis inside S, and was not used. The existing face-localization and sharpening nodes assume a face and do not directly apply to the image of a general chart; the explicit calculation in Step 2 avoids an unjustified citation of them.

## Review by Q10

I checked the statement against the actual ILO nodal chart, and distinguished its general algebraic refinement from that specific source example. There is no statement dispute: all original hypotheses and conclusions are retained. I checked the exact definition of fs and group completion in def-trf-fs-log-blowup; it supplies the integrality and saturation used here. I read the current chapter and unit records and the current blueprint locality proof, preserving the historical ancestry without changing any higher-level route. There are no new nodes whose hypotheses or literature attribution would need independent checking.

Step 1 uses def-trf-fs-log-blowup for the embedding in the group completion and finite monoid generation, and lem-trf-fg-torsionfree-group-free for a finite integer basis. Its statement explicitly assumes finite generation and torsion-freeness; the former is proved using images of the monoid generators and the latter is a hypothesis of the item. This basis is initially arbitrary, so the proof does not prematurely assume that it lies in Q or S.

Step 2 uses exactly the saturation clause of def-trf-fs-log-blowup. The lift x lies in Q^gp, the integer n is positive, a,b lie in P, and g(a),g(b) lie in Q. Thus n(x+g(b)) lies in Q and all hypotheses of that clause are checked. The image calculation is written in full, rather than cited as a quotient-saturation theorem.

Step 3 uses the full rectangular Cauchy–Binet statement and the determinant's defining formula. B has r rows and m columns and C has m rows and r columns; BC is the r by r identity. Thus this is precisely the statement of the cited node over the commutative ring Z, including its empty-sum convention when m<r. The determinant definition supplies det I=1. Step 4 only uses integer values of that formula and the elementary least-positive-integer principle, with nonemptiness already supplied by Step 3.

Step 5 uses the actual two-sided adjugate identity over Q; dividing by the nonzero determinant gives the asserted inverse and independence. No theorem about arbitrary fundamental domains is used. The integer y is chosen only under the proper-span assumption, z is integral by the defining floor inequalities, x=y-Az is integral, and a is rational with each coefficient in [0,1). Not-all-zero follows from y being outside the integer column span. This is the explicit elementary calculation following the cited adjugate identity.

Step 6 first applies the saturation proved in Step 2, with a positive common denominator and nonnegative integer coefficients; x belongs to the lattice, so saturation's ambient-group hypothesis holds. Its two cited nodes give the square Cauchy–Binet formula over Q and the precise determinant sum used to compute det E. The resulting replacement matrix has integer entries despite the rational intermediate E. The strict inequalities require a_j>0 and a_j<1; both came from Step 5. The contradiction is therefore against the same positive integer D minimized in Step 4, not a real-valued minimum. Steps 7 and 8 are elementary basis-coordinate and quotient-kernel calculations; every existence and uniqueness statement is written out.

Step 9 uses def-trf-fs-log-blowup solely for integrality and the group-completion generator relations. It explicitly checks that the formula lands in Q, that it restricts to g, that equality of h-values reduces to injectivity of Phi, and that group completion of P times N^r is P^gp times Z^r by its universal property. Thus the isomorphism proved for Phi is precisely h^gp rather than merely an unrelated splitting of the group extension.

For small cases I checked r=0 (including P=Q={0} and any g^gp isomorphism), P={0}, Q=N, non-sharp Q=Z, and groups with torsion units such as Q=N times Z/2 with P=Z/2 embedded as the units. The proof needs torsion-freeness only for L, not Q^gp. For a non-face image, P=N -> Q=N^2, 1 maps to (1,1), the quotient image S is Z, so the face lemmas cannot be applied directly but Step 2 works. For a non-unimodular tuple in the saturated monoid N^2, the columns (1,0),(1,2) have determinant 2 and the floor construction gives x=(1,1) with coefficients (1/2,1/2), reducing the determinant to 1. For r=1 and A=(-2), choosing y=1 gives a=1/2 and x=-1, so negative coordinates and determinant signs cause no problem. Without saturation, Q generated by 2 and 3 in Z, P={0}, would fail to contain either Z-basis vector 1 or -1; this confirms that the saturation hypothesis is doing necessary work.

Against delivery-errors B–E: there are no statement-only new nodes to check or duplicate; TeX is singly represented in the decoded strings; source tags were checked in the local tag map and tex; every non-elementary external input has an existing node whose statement I read and quote. Cauchy–Binet is declared as an off-unit generic tool in split_report.tool_uses because this unit has no matrix theorem supplying it. No dependency points back to this item, no clause is repackaged as a new node, and all intermediate algebraic comparisons are written explicitly. All nine proof steps are shorter than 1000 characters, so there is no >2000-character step hiding a lemma.

## What could not be finished

Nothing mathematical remains in this one-level split. Delivery validation and push are recorded below after the required tools finish.

## Delivery validation

The required `deliver.py Q10 lem-trf-fs-chart-free-factorization --no-push` exited 0 and printed `OK (not pushed)` at commit `8f64a76ac9`; server preflight passed. The delivery uses the direct-delivery worker's self-review above; the maintainer's independent review follows the push.
