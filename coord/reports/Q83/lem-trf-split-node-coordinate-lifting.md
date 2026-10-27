## Worker report

1. File written: `dag/nodes/sec-trace-formula/lem-trf-split-node-coordinate-lifting.json`, statement, now split; no exact Mathlib match. No new node files. `citations.json` contains the verbatim full statement of each node cited in each proof step. `searches.jsonl` records the five new searches actually run.
2. Attachments: none. Searched `lean/WeilConjectures/` by the blueprint tag and by split-node/nodal-coordinate vocabulary; no declaration states the item. The related `lean/Sheaf/TraceFormula/FormalLocalStructureNodalFamily.lean` is the parent geometric presentation theorem, not an attachment for the quantified sequences of this item.
3. WANTED: none.
4. The item was statement-only, with searches from its parent's earlier split. Its statement is kept byte-for-byte. The source display writes x for both variable images; the second is y. This already has the intended reading in the item and requires no statement correction. The source's "Since A and B are complete" is now justified for the actual maximal-ideal topologies. In particular, preserving reductions modulo mB needs separatedness of B/mB, not just convergence in B; this is supplied by the existing complete-local-quotient node.
5. Nothing mathematical remains unfinished in this one-level split. Dry-run and delivery results are recorded below when available.

## Sources and searches

Read the full statement and proof of Stacks `curves.tex`, Tag 0CBX, `lemma-formal-local-structure-nodal-family`, especially its finite coefficient decomposition, correction formula, induction, and passage to limits. Read `algebra.tex`, Tag 0325, `lemma-quotient-complete-local`, including the first sentence and proof, and the exact statement and definition nodes used below. Also read the parent N8 report, which preserves the original three steps for this extracted item.

Read the chapter/unit records and the latest blueprint chapter, unit and ancestor files beneath `literature/blueprint/latest/`. The nearest blueprint ancestor is `lem-trf-local-term-locality`, but the nodal chart chain is a historical input: its algebra here does not change the latest contracting-correspondence proof. No unit or chapter record is changed and no SGA route is used.

Searched the whole DAG for 0CBX and for complete local quotients, convergence, closed ideals and power series; read the parent and existing quotient theorem. Ran `tools/blueprint_refs.py ancestor lem-trf-split-node-coordinate-lifting` and whole-blueprint searches for formal local, split node, split-node, node coordinate, coordinate lifting, Krull intersection, adic convergence and complete local quotient (also the broader coordinate and complete local searches). None states this quantified coordinate-lifting theorem. No proposed new node survived: the only non-elementary external theorem needed already exists.

The five 2026-10-23 searches in `searches.jsonl` were all successful: LeanFinder with two distinct phrasings, Loogle `MvPowerSeries, IsAdicComplete`, grep `nodal|splitNode|coordinate.*lift|lift.*coordinate`, and LeanSearch for successive lifting of the node coordinates. Read the returned types. Weierstrass division/preparation are one-variable factorization statements; simple-root Hensel and StandardEtalePair have invertible-derivative/etale hypotheses unavailable at a node; the perfectoid untilt statement is about its specified untilt sequence. The Loogle hit is completeness of the fixed formal power-series ring for the variables ideal. Localization lifts and Lagrange interpolation likewise do not produce the sequences in the item. These facts are not an exact match or a one-line specialization. Kept the inherited searches and added only the queries actually run, with their returned names and honest no-match verdicts; no unavailable service is recorded as absence.

## New nodes

None. All the coefficient manipulations, finite-sum corrections, recursion, stabilized-residue construction and congruence calculations are explicit proof steps. The existing quotient theorem is reused instead of making a closed-ideal lemma.

## Review by Q83

I checked delivery-errors B through E against the actual item, cited statements and source texts. There is no new statement-only node to audit, no duplication, no proof relocated into a new clause node, and no unlogged search. All TeX is single-escaped after JSON decoding. Each proof step is under 2000 characters. I kept all imported and maintainer fields unchanged.

Step 1 uses the hypothesis theta, the definition of a unit and the local-ring maximal ideal. In the split-node quotient a multiple of x or y has zero constant term, while the class of 1 does not; hence any lift is a nonunit, and therefore belongs to n. This avoids assuming unproved locality of an arbitrary power-series homomorphism. Their product lies in mB, so h_1=0 works for every prescribed initial pair.

Step 2 cites `def-weil-pbc-multivariate-power-series`, whose statement gives the coefficient families and finite convolution product. Its constant term and the partition of the remaining monomials give F=c+xP+yQ directly. Each scalar c lifts along A -> k and each class of P,Q lifts along B -> B/mB. Consequently the claimed decomposition of every b is an actual equality with a remainder in mB. It does not require a coefficient field embedded in A or B, or a formal-substitution theorem.

Step 3 uses the previous decomposition and only finite ideal sums and ring arithmetic. I recomputed the signs: subtract Q_r from u_r and P_r from v_r, then add sum f_i a_i to h_r. The error is sum alpha(f_i) epsilon_i + Q_r P_r; both terms lie in m^(r+1)B, the latter because 2r >= r+1 for r>=1. The finite expression of an extended-ideal element is its definition. Corrections keep the fibre classes and membership in n, and h stays in m since m^r is contained in m. Recursion uses this improvement at every positive index, not an unestablished inductive assertion. No flatness or characteristic restriction enters.

Step 4 cites `def-weil-pbc-adically-complete-ring`, which states bijectivity onto the inverse limit and includes intersection of ideal powers equal to zero. Telescoping gives differences in the indicated powers, so the compatible stabilized residue classes exist. Completeness produces their unique representatives and precisely the convergence asserted by the item. Taking the first quotient ensures u,v belong to n and h belongs to m. Locality alpha(m) subset n gives the necessary inclusions in powers; mB-adic completeness is never assumed.

Step 5 cites `lem-weil-pbc-complete-local-quotient` and that completeness definition. I read its full statement: a proper quotient of a complete Noetherian local R is complete at the quotient maximal ideal m_R/I. Here R=B satisfies all those assumptions and I=mB is proper because it is contained in n. Thus B/I is separated for n/I. For every N the limit difference u-u_1 is in I+n^N, so its quotient class is in every (n/I)^N and is zero. The identical argument for v keeps both specified fibre coordinates. This is exactly the statement of the cited theorem, not an uncited consequence extracted from its proof. This generic theorem is declared as an off-unit tool in split_report.tool_uses.

Step 6 again cites completeness only for its explicit separatedness clause. The formula uv-u_rv_r=(u-u_r)v+u_r(v-v_r) proves multiplicative compatibility modulo each n^N without a hidden continuity lemma. The base difference maps into n^N because alpha is local. Adding the known error shows uv-alpha(h) is in every n^N, hence zero. Each external use is represented by a verbatim statement in citations.json, and proof_deps is precisely the union of the uses.

I tested the formulas with m=0 (the starting product is already zero and the sequences can be constant), A=k[epsilon]/(epsilon^2) (the first corrected error is zero), characteristic 2 (no division or negative-sign distinction is needed), noninjective alpha (all elements of A are explicitly mapped by alpha), and B=A[[x,y]]/(xy-t) for A=k[[t]] (the ordinary smoothing case). Arbitrary initial lifts are allowed in the formulas. The case r=1 meets 2r>=r+1 at equality. There are no new hypotheses, no need for B to be flat over A, and no inversion of 2. I found no statement dispute.

## Not duplicates

No new nodes. The quotient theorem is cited as-is; the parent geometric nodal-presentation theorem is strictly stronger in geometric conclusions and lacks the arbitrary-start, controlled-sequence statement, so it is not used circularly. The proof has no dependency on its parent.

## Validation

Required server dry run exited successfully: `OK (not pushed) deliver/Q83/lem-trf-split-node-coordinate-lifting at c6349b974a6: preflight passed`. This includes the server DAG and split checks. Local read-only comparison also confirmed the statement is byte-identical, only split-owned fields changed, and all citation quotes are verbatim. Direct delivery follows this successful dry run.
