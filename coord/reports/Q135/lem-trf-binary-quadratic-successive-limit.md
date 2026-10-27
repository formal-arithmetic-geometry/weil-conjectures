# Q135: lem-trf-binary-quadratic-successive-limit

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-binary-quadratic-successive-limit.json`: statement; split into eight explicit steps; no exact Mathlib match.
- `citations.json`: one verbatim statement quotation for each node used by each step.
- `searches.jsonl`: unmodified results logged by the required msearch command.
- `report.md`: this report. `prepare.py` is a sandbox-only JSON preparation script and is not a DAG delivery file.

New nodes: 0. New Mathlib leaves: 0. The existing Mathlib leaf for variable-adic completeness is reused. No unit or chapter record is changed: this item is not its unit's key statement.

## Attachments

None. Searches in the project `lean/WeilConjectures/` for the item's blueprint tag, binary quadratic limits, successive limits and tangent-to-identity coordinates found no declaration stating the item. Related project power-series and first-order comparison declarations do not state its successive limits, inverse coordinates or quadratic congruence. No sorry-bearing declaration is treated as a finished proof.

## WANTED

None. The relevant Stacks source is present. The detailed specialization and inverse calculation are explicitly agent-written, not attributed to an omitted Stacks proof.

## What needed work

The live item was unsplit and had no proof; the sandbox had no earlier item or report. I retained its statement, source, inherited searches and blueprint ancestry. There is no statement dispute. Stacks Curves 0C49 (`lemma-nodal-algebraic`), proof of (2) implies (3), passes from successively higher-order corrections to a limit using completeness, but does not state this specialized automorphism theorem. The new proof records that distinction through `proof_origin.by = agent` and supplies the missing inverse calculation explicitly.

The latest blueprint ancestor `lem-trf-local-term-locality` and latest `sk-i-curve-zero` concern contracting local terms. The item reaches them through its inherited pointwise nodal-completion ancestry; I preserve that route and refine only the formal-power-series argument already required by `lem-trf-formal-binary-morse`. I have not changed the chapter or unit route or claimed that the latest blueprint ancestor itself contains a formal inverse theorem.

## What remains unfinished

Nothing in this stage-1 item. Its downstream inputs already exist; their future Lean formalization is outside this delivery. Dry-run and push results are recorded below when available.

## Not duplicates

No new nodes were created, so there are no new/existing pairs to distinguish. I searched the whole DAG for variable-adic completeness, coefficient criteria, formal substitution, invertible linear parts, tangent-to-identity automorphisms and filtered geometric inverses. Blueprint searches (`power series`, `automorphism`, `filtered`, `geometric series`, `0C49`, `successive`, `substitution`, `quadratic`) yielded no equivalent blueprint statement; the item's `same_as` is therefore empty. The existing combined-ideal coefficient criterion, variable completeness and adic evaluation are cited directly instead of duplicated.

## Review by Q135

I read Curves Tag 0C49 in `literature/stacks-project/curves.tex`, including its induction, summation and resulting power-series map. Its nondegeneracy hypothesis is needed to produce the corrections upstream, not for the limit theorem once corrections are given. This justifies retaining the item's assertion for arbitrary a,b,c and every characteristic. I read the complete current statements of all five cited nodes (including the two definitions), not their titles or proof sketches. No new node requires a separate source review.

Step 1 uses `lem-weil-pbc-power-series-combined-ideal-coefficients` with J=0, d=2. For |E|<N the exponent N-|E| is strictly positive, so membership in that power of the zero ideal means coefficient zero. This also handles N=0 through the empty condition. The exact statement of `lem-weil-pbc-power-series-variables-complete` permits every commutative coefficient ring and any finite number of variables; F and two variables meet it. `def-weil-pbc-adically-complete-ring` explicitly identifies completeness with bijectivity onto the compatible quotient system and includes separatedness. These are exactly the coefficient, lifting and uniqueness facts used, and are quoted verbatim in citations.json.

Step 2 uses `def-weil-pbc-multivariate-power-series`, which defines series as arbitrary coefficient families. The increment congruences imply coefficient stabilization by finite telescoping, so the eventual coefficients define actual data, with no chosen object coming from an unspecified existence theorem. The coefficient criterion already established in step 1 gives the precise tail bounds, uniqueness and the initial congruence. The indices are r>=2 throughout; for degrees 0 and 1, r=2 already suffices. The statement's phrase r>d is understood among its given sequence indices r>=2.

Step 3 uses `lem-weil-pbc-power-series-adic-evaluation`: it states the map, its images on constants and variables, its continuity, and the finite-truncation congruences. Its input is a commutative complete target with variable images in I. Step 2 puts both images in p; the separately cited completeness leaf supplies the required target hypothesis. The coefficient map is the actual constant-series inclusion, so the resulting ring map is an F-algebra map. This node says more than mere existence of a ring map and really includes the formula used in step 4.

Step 4 uses no uncited inverse theorem. On each monomial, replacing one degree-one factor by h_1 or h_2 in p^2 raises total degree by at least one; a finite binomial expansion proves the claim in every characteristic. The finite-truncation formula from step 3 and coefficient vanishing from step 1 yield D(p^k) subset p^(k+1). The k=0 case is checked separately through constant coefficients. This is a finite calculation from the earlier interfaces, not a hidden general convergence lemma.

Step 5 is the finite identity (1-D_M)(1+D_M+...+D_M^(M-1))=1-D_M^M=1, in both composition orders. Nilpotence follows by M repetitions of the explicit degree bound of step 4, starting with p^0. Multiplicativity of the inverse follows by applying the injective ring map b_M, rather than assuming that a sum of linear maps is multiplicative. I checked quotient compatibility explicitly; the extra last term vanishes after reduction because D_M^M=0. This avoids an unexplained transport or a choice of incompatible inverses.

Step 6 cites the same completeness leaf and its precise definition for the actual compatible residues constructed in step 5. Comparing their residues gives both inverse identities and the algebra laws; separatedness proves equalities. It uses neither noetherianity nor a claim that a surjective endomorphism is automatically invertible. Step 7 proves preservation of each p^N for the inverse using its residue at level N, and preservation for the forward map follows from step 4. Continuity at all points then follows directly from additivity and the given neighbourhood basis; N=0 is explicitly included.

Step 8 writes the exact quadratic difference identity. Each error factor is in p^r, and each accompanying coordinate factor is in p, giving p^(r+1), including r=2. The exact limit identity follows by coefficient separatedness, since the exponents r+1 are unbounded. The beta(Q) equality uses its actual algebra-map images, not an unproved statement about arbitrary infinite evaluations. I checked the zero quadratic, a single square, pure mixed term, characteristic 2, a stationary sequence, and nonstationary increments of exact order r; none requires a discriminant hypothesis or division by 2. I also checked the quotient M=1: b_1 is the identity on constants, D_1=0, T_1=1, so the inverse system starts correctly.

Against delivery-errors B--E: statements and notions were retained, all non-elementary inputs already exist and were opened, all actual searches were logged as returned, no duplicate or clause-restatement node was introduced, and no cycle is introduced by using the generic proper-base-change algebra tools. The coefficient and evaluation nodes are off-unit generic tools, so `split_report.tool_uses` declares precisely their black-box purpose; the completeness leaf and definitions are tools automatically. All non-elementary steps are shorter than 2000 characters, as are the explicit elementary calculations. Every node appearing in a step's uses has a verbatim quote, and proof_deps equals their union. No SGA source, Lean edit, compiler, Lake command, repository write or repository git command was used.

## Validation and delivery

Server `review_split` passed with 0 new nodes. Full `deliver.py --no-push` exited successfully: `OK (not pushed)` at 53be176075d, including server preflight and DAG checks. The final delivery follows a repeat dry run covering this report update. The server noted that the containing unit has no realization recorded yet; this non-key item does not own that unit record.
