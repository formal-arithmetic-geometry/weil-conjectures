# Q39: lem-per-flat-integral-total-fractions

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-flat-integral-total-fractions.json`: statement item, now split in seven steps; whole-item Mathlib verdict: no match. The statement and `stmt_deps` are unchanged. All inherited searches and metadata are retained; five Q39 searches are appended.
- `citations.json`: fourteen entries, one for each step/node citation, quoting the cited statements verbatim.
- `report.md`: this report. `searches.jsonl` is the search command's own record.

New nodes: 0. New Mathlib leaves: 0. No Lean, repository, launcher, chapter or unit file was written, and no compiler or git command was run directly.

## Attachments

None for the item. Searching `lean/WeilConjectures/` by the blueprint tag and the notions found no declaration stating all clauses. The existing theorem `integral_totalFraction_mem_range_of_normal` in `WeilConjectures/RingTheory/NormalRingIntegrallyClosedTotal.lean:46` proves the existing dependency `lem-weil-pbc-normal-ring-integrally-closed-total`, not the item. Its full signature and proof were read.

## WANTED

None. All sources used are present.

## Findings and corrections

The imported item has a correct statement but no proof. Its reference to a previously split finite comparison is useful source material, not a permissible application: `lem-trf-flat-birational-normalization-comparison` assumes that B is a finite A-module, which this item explicitly does not assume. The proof instead clears the finitely many denominators in one tensor element at a time. It uses neither a global denominator for B nor finiteness of normalization. No statement correction or statement dispute was needed.

I read the current blueprint under `literature/blueprint/latest/` (main-20261024), including the ancestor `lem-per-artin-gabber-affine-curve`, and the chapter/unit records. This auxiliary algebra item serves Steps 5--7 of its parent `lem-per-normalized-tower-regular-pullback`: integral flat scalar extension of normalization, its total-fraction identification, and the normal case. It changes no unit or chapter route. The current ancestor does not spell out the intervening modification algebra; the precise parent and ILO source record that auxiliary ancestry.

## Searches and existing nodes

Whole-DAG searches for the total-fraction, flat tensor injection, integral base change, localization and normality statements found all inputs already represented. The blueprint reference tool's searches for `total fraction` (zero blueprint nodes) and `birational` (the two curve normalization nodes, which require integral schemes of finite type over a field) found no equivalent blueprint assertion. No new nodes were created.

All five Q39 Mathlib searches were executed with the required msearch command and their results read. The second LeanFinder phrasing explicitly asked about arbitrary nonfinite intermediate algebras. LeanSearch returned `Algebra.IsIntegral.tensorProduct`, `Algebra.TensorProduct.includeLeft_injective`, and flat-tensor lemmas, covering only parts. Loogle `TensorProduct, IsFractionRing` returned a Picard-group lemma. The grep returned the integral-closure tensor comparison and algebraic fraction base-change declarations. I read `RingTheory/Smooth/IntegralClosure.lean:30--115`, `RingTheory/Algebraic/Integral.lean:500--531`, `RingTheory/Flat/Basic.lean:120--142`, and `RingTheory/IntegralClosure/Algebra/Basic.lean:245--257`. The first comparison has source the full integral closure and target inside a tensor product, not the stated arbitrary intermediate algebra inside Q(R). The algebraic result assumes `NoZeroDivisors S`; it does not cover general reduced rings with zero divisors. Neither gives the complete item by one specialization. Existing leaves handle the flat-tensor and integrality inputs, so no duplicate Mathlib node was made. The inherited searches are retained as historical metadata; the appended records are exactly the Q39 commands recorded in searches.jsonl.

## Not duplicates

No new nodes. In particular the finite comparison remains a distinct existing result with a finite-module hypothesis and global denominator conclusion; it is not cited as if it applied here.

## Review by Q39

I read Stacks `algebra.tex`, localization construction before 00CP and at 07JZ, 00CP and its proof, 00CX and the generating/balancing construction of tensor products, 00HB and 00HD, 02JK(1) and its monic-generator proof, and 034M and its denominator-ideal proof. I verified these tags against `stacks-project/tags/tags`. I also read ILO Exposé VIII 2.2.1--2.2.10, printed pp.90--91 (PDF pp.96--97). Lemma 2.2.9 reduces normalized pullback to an integral generically-isomorphic comparison with a normal target. It does not state this non-Noetherian algebra generalization verbatim. Accordingly `proof_origin.by` is `agent`: the explicit calculation expands that source's algebra using the cited Stacks facts. There are no new-node sources to audit.

For Step 1 I opened the statements of `def-weil-pbc-module-localization`, `def-weil-pbc-flat-ring-map`, `lem-trf-flat-tensor-preserves-injection`, `def-weil-pbc-module-tensor-product`, and `lem-weil-pbc-ring-localization-universal-property`. Localization gives precisely its kernel criterion and unit denominators. The injection leaf applies to R as a flat A-module and to each of the A-linear maps multiplication by s on A and on B. The latter map is injective because B is an actual subalgebra of Q(A), where s is a unit. The tensor identifications and inverses are written down. This proves regularity both on R and on C, rather than inferring it just from the definition of flatness. The localization universal property then has all its unit hypotheses.

Step 2 uses the opened tensor-pushout statement, whose clause (2) constructs a ring map from the two algebra maps agreeing on A; its formula proves the R-algebra assertion. The already proved injection R to Q(R) gives injection R to C from the composite. No faithful flatness is assumed.

Step 3 uses the opened tensor definition's assertion that pure tensors generate, and the opened localization definition's fraction representatives. I checked the explicit formula s b_h = a_h times the product of the other denominators inside B and then the balancing formula in C. Multiplication by f(s) is injective by Step 1. Thus the elementary finite-sum calculation proves injection of j without assuming a global denominator or quoting a hidden finite-generation argument. This step does not assert a separate general theorem with its own hypotheses.

Step 4 cites the opened statement `lem-weil-pbc-integral-base-change`, which says exactly that R tensor_A B is integral over R for r mapping to r tensor 1. Its hypotheses are just the assumed integral A-algebra B and the given ring map A to R. It imposes neither Noetherianity nor finiteness.

Step 5 uses only the opened fraction definition and previously proved embeddings. I checked both directions needed for localization: a regular element of R stays regular on C because it is a unit in Q(R); a regular t in C has j(t)=r/u, and the equation ut=r in C forces r to be regular in R. The displayed inverse u/r is therefore available. The argument does not identify all regular elements with nonzero elements, which would be false with zero divisors.

Step 6 cites the opened ring-localization universal property for existence, formula, and uniqueness, and the opened fraction definition. Step 5 verifies both sets of units. JH agrees on R; HJ agrees on each c using the equation uc=i(r), and then on Q(C) by uniqueness. I checked both composites rather than claiming an unexplained canonical identification.

Step 7 cites the opened integral-closure definition for monic equations and the opened normal-ring integral-closedness statement (034M). That statement says every integral element of Q(C) lies in the image of C for an arbitrary commutative normal ring. The normality assumption is imposed only here, exactly as in the item. Applying H to the R-equation makes H(x) integral over C with the displayed coefficients; applying J returns x=j(c). Conversely applying j to an integral equation for c gives the inclusion from Step 4. This is the sole off-unit generic tool; it is declared in split_report.tool_uses, with no top-level tool_uses field added. No SGA source is used.

I checked delivery-errors B--E in full: no new-node shape issue, no fabricated search, no same-clause placeholder nodes, no unsupported non-elementary fact, no use of a cited node's proof instead of its statement, and no changed coefficient or ring objects. Every cited node was opened and its full statement is quoted in citations.json; the proof dependency list is the union of the actual step citations. Every step is below 2000 characters. The finite-denominator calculation is an elementary argument from the stated tensor/localization formulas and Step 1, not a hidden external lemma.

Small-case checks: B=A yields C=R and the identity on total fractions. For A=k times k mapping flatly onto its first factor R=k, the map need not be faithfully flat or injective, but regular pairs still map to units; all claimed embeddings of R and C remain valid. For the reduced nodal ring k[x,y]/(xy), with B=k[x] times k[y] and R=A, regular denominators and both fraction inverses agree in k(x) times k(y). The zero-ring case uses no nonempty spectrum, nonzero denominator, or field assertion: multiplication on the zero module is injective, and all constructions are zero as required.

For an explicit nonfinite test, take the monomial subrings
$A=k[t^q:q\in\mathbf Z[1/2]_{\ge0},\ q=0\text{ or }q\ge1]$
and $B=k[t^q:q\in\mathbf Z[1/2]_{\ge0}]$ in the fraction field of the monoid algebra. Every monomial $t^q$ in B is integral over A, since for q>0 some positive integer multiple of q is at least 1; the q=0 monomial is 1. Since integral elements form a subring, B is integral over A. Also $t^q=t^{q+1}/t$ lies in Q(A). If B had finitely many A-module generators, the finitely many monomials in their supports would supply all exponents below 1 of every A-linear combination: any nonconstant monomial of A has exponent at least 1, and the generators have nonnegative exponents. But B contains the infinitely many distinct exponents $1/2^n$. Thus B is not finite over A. Both rings are domains and R=A is flat, so the split applies. In particular this verifies that the proof never needs a finite A-module generating family for B.

## Unfinished work

None in the mathematical split. The required server dry run passed; the final report revision is validated again before direct delivery.
