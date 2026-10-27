# Stage-1 report: lem-trf-integer-matrix-fractional-lattice-witness

## Files written

- dag/nodes/sec-trace-formula/lem-trf-integer-matrix-fractional-lattice-witness.json: existing statement, now split into four proof steps; no exact or one-line Mathlib match.
- citations.json: the verbatim adjugate-identity statement used in step 1.
- report.md: this report. searches.jsonl is the unmodified record produced by msearch.py.

New nodes: 0. New Mathlib leaves: 0. The proof reuses lem-weil-pbc-matrix-adjugate-identity, an existing Mathlib leaf. Statement, source, statement dependencies and ancestry are retained. No maintainer-owned fields, Lean source, unit or chapter files were changed.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and the integer-matrix, rational-coordinate, fractional-lattice, ZSpan, adjugate, nonsingular and parallelepiped notions. No declaration states the full item. Related finite-free matrix lemmas concern different objects or hypotheses. No compiler or build command was run.

## WANTED

None. The existing source is present. This is explicitly an agent-supplied elementary refinement, not a claim that Stacks states the floor construction.

## Findings and corrections

The imported node had a complete true statement but no proof. Its reference to Stacks 07DQ supplies only the adjugate identity, and that distinction is retained. I supplied the rational inverse and floor-remainder argument explicitly, with proof_origin.by = agent. No statement dispute or change was necessary.

I read dag/chapters/sec-trace-formula.json, dag/units/sk-i-curve-zero.json, and the latest blueprint files for sk-i-curve-zero and lem-trf-local-term-locality (statement and proof). The current blueprint local-term proof is a contracting-correspondence argument, not a source for this arithmetic lemma. The node already records its historical nearby-duality/alteration/chart-factorization ancestry; I retained that exact lineage and described the auxiliary place in split_report.blueprint. No unit or chapter route is replaced here.

The original search records from Q160 were retained, read and supplemented with actual NM msearch.py searches, including two semantic phrasings, Loogle, LeanSearch and source grep. Read ZSpan.fract_mem_fundamentalDomain (Mathlib/Algebra/Module/ZLattice/Basic.lean:194), the fundamental-domain definition (91--96), floor/fract definitions and coordinate formulas (130--195). These assume a supplied basis. They do not directly provide a rational basis from the integer matrix, the unique coordinates, or both integrality and nonvanishing of the representative. The small-vector number-field hits have different hypotheses. The item therefore needs the assembly proof rather than a Mathlib-leaf label. Also read the floor inequalities at Algebra/Order/Floor/Defs.lean:301 and Floor/Ring.lean:129; they match the defining inequalities already in the item.

## Not duplicates

No new nodes were created. Whole-DAG statement/title searches for floor, adjugate, nonsingular matrices, determinant invertibility and column lattices found the existing adjugate identity, which is reused. Whole-blueprint searches for matrix, floor, parallelepiped and adjugate found no equivalent item. tools/blueprint_refs.py ancestor confirms lem-trf-local-term-locality as the inherited nearest blueprint ancestor. The existing determinant definition and adjugate leaf were opened and read, not inferred from their titles.

## Review by NM

I checked the split against delivery-errors.md B through E, including both copies in that document. For the item source I read literature/stacks-project/algebra.tex, the lemma-matrix-left-inverse statement and proof, especially lines 2688--2691. I verified Tag 07DQ maps to algebra-lemma-matrix-left-inverse in tags/tags. There are no new-node sources to review. For the sole cited proof dependency I read the entire statement of lem-weil-pbc-matrix-adjugate-identity and its Mathlib match, then read Matrix.mul_adjugate and Matrix.adjugate_mul at Mathlib/LinearAlgebra/Matrix/Adjugate.lean:264 and 269. Its statement supplies both BA = delta I and AB = delta I, exactly what step 1 needs; citations.json copies that whole conclusion verbatim.

Step 1 applies this identity over Z, a commutative ring, to the square r by r matrix. The determinant is the same Leibniz determinant defined by def-weil-pbc-matrix-determinant (its full statement was read). I deliberately apply the identity over Z and embed the resulting finite entrywise equalities into Q; no separate unquoted base-change determinant theorem is used. Since delta is a nonzero integer, it is a nonzero rational, so dividing B by delta gives a two-sided inverse. The only non-elementary statement in the proof is the cited adjugate identity.

Step 2 uses the explicit two-sided inverse from step 1. Multiplying Ac = 0 by C proves column independence. Taking b = Cy proves existence for every y, and multiplying any other equation Ab' = y by C proves uniqueness. It does not assume that the integer columns form a Z-basis; that would contradict the possible hypothesis on y.

Step 3 uses the defining floor inequalities already written in the item, with their concrete Euclidean quotient interpretation included for a rational p/q with q positive. Subtracting z_i gives the bounds on a_i. The argument explicitly allows p negative, and uniqueness follows because distinct integers differ by at least one. These are elementary arithmetic operations, not a hidden lattice theorem or a newly named clause of the item.

Step 4 writes the matrix linearity calculation Aa = Ab - Az = y - Az. Integrality follows entrywise from integral y, A and z. Nonvanishing is proved directly: x = 0 would put y = sum z_i v_i in the excluded integer span. Some coordinate of a is nonzero because Aa is nonzero; its previously proved bounds make it strictly positive and less than one. No integrality of b or a, nonnegativity of matrix entries, positivity of det A, or finite-index theorem is assumed.

Small cases checked by hand: r = 1, A = (2), y = 1 gives b = 1/2, z = 0, a = 1/2, x = 1. With y = -1 it gives b = -1/2, z = -1, a = 1/2, x = 1, checking the negative floor case. With A = (-2), y = 1 it gives b = -1/2, z = -1, a = 1/2, x = -1, checking the determinant sign. With A = diag(2,1), y = (1,0), only the first fractional coordinate is positive, as allowed. For A = I the column-independence assertion remains true and no y satisfies the outside-span hypothesis. The restriction r >= 1 is retained; no argument silently chooses a coordinate from an empty family.

Every step is shorter than 2000 characters and the entire assembly proof is shorter than 3000. No content was moved into a new node, no unsplit node was cited for an internal proof, no off-route non-leaf theorem was used, and there is no dependency cycle introduced. The only proof dependency is an existing Mathlib leaf; the union of the steps' uses is exactly proof_deps. B's self-contained-statement, source, TeX, search and blueprint requirements, C1/C4's coverage and statement-match requirements, D's no-relabeling requirement and E's hypotheses, object and explicit-calculation requirements are all met.

## Unfinished work

None in the stage-1 split. Independent maintainer review remains the normal review of the delivery.
