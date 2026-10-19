## Files written

- `dag/nodes/sec-trace-formula/lem-trf-proj-twist-section-basic-open.json` — statement, split in four steps; no Mathlib match. No new nodes or Mathlib leaves.
- `citations.json` — one verbatim statement quote per step/node citation.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` by the exact blueprint tag and id found no declaration. Concept searches found `Proj.compl_support_zeroLocus_unitToTwist` in `AlgebraicGeometry/ProjectiveSpace/CoordinateSection.lean:58`, which assumes degree-one standard opens cover all of Proj and only treats a degree-one section; it does not give the present arbitrary-degree W_d statement or its basis clauses. I read its hypotheses and proof. `isFreeGenerator_twist_of_mul_eq_one` in `AlgebraicGeometry/ProjectiveSpectrum/Twist/TensorObj.lean:54` supplies a general generator method, not the complete item. The reference master source is not treated as evidence of a finished proof.

## WANTED

None.

## Errors found and changes made

The imported source pointer calls `lemma-where-invertible` Tag 01MS. The actual local tag table gives 01MS = `lemma-when-invertible` and 01MU = `lemma-where-invertible`; I corrected this bibliographic error. The statement is unchanged. I added `def-weil-pbc-ample-invertible-module` to the statement dependencies because it defines the nonvanishing locus used in the statement. The proof uses that definition, not any ampleness assertion.

The initial candidate chart-calculation child would have packaged a short calculation already following from the twist definition. I removed it and wrote that calculation in Step 1. The original draft's bare affine-basis appeal also needed a precise refinement: an arbitrary U intersect D_+(f) need not be affine. Step 3 now chooses D_+(g) contained in the prescribed open of U, so Step 4 applies affineness to that whole ambient standard open. There are no new nodes and hence no duplicate pairs to justify.

## Review by Q98

I read `dag/chapters/sec-trace-formula.json`, the assigned unit `sk-i-curve-zero`, the inherited blueprint ancestry and the parent `lem-trf-proj-qc-open-twist-ample`. This item is the section-algebra/Proj ampleness input recorded under `lem-trf-local-term-locality`; it remains on that route. I searched all DAG chapters and the imported blueprint with `blueprint_refs.py`, including principal-open, homogeneous-section and twisting-chart phrases. The existing polynomial-P1 section node has stronger special hypotheses, and the existing generic chart-intersection node is exactly the needed input, so no new node is justified. I retained the inherited mathlib searches, appended the real search-log entries from this run, tried a second semantic phrasing and a valid quoted-name Loogle query, and read the returned structure-sheaf and chart API hits. None concerns twist nonvanishing on W_d. The source-only twist and coordinate-section hits do not state the complete item.

For the item I read Stacks `constructions.tex`, `lemma-where-invertible` (01MU), `lemma-principal-open` (01MV), and `lemma-ample-on-proj` (01MW), including the proofs, and checked the tag mapping. The statement agrees with 01MV restricted to an arbitrary open U of W_d; the 01MW basis conclusions require neither quasi-compactness nor a special finite-cover choice once U is already inside W_d. No generation-in-degree-one hypothesis is used.

Step 1 cites the statement of `def-weil-pbc-proj-twisting-sheaf`, which explicitly gives sections as the degree part of A_h, their restriction maps as localization homomorphisms, and the canonical section as f/1. I checked these three clauses in that node. The union characterization of W_d is already a hypothesis of the item. On a chart h=ab, a and b are units in A_h and e=(a/b)^n has inverse of opposite degree. Multiplication by these fractions gives mutually inverse module maps on chart sections, compatible with restriction, so it trivializes the sheaf. This is the full elementary argument; no unnamed trivialization theorem is hidden here.

Step 2 cites `def-weil-pbc-ample-invertible-module` for the exact maximal-ideal definition of nonvanishing, and `lem-weil-pbc-proj-basic-open-intersection` for its explicit unit-germ characterization of the intersection with a homogeneous standard open. I read both statements. To check the latter's hypotheses I set its chart element to h=ab of degree k=alpha+beta>0 and its other element to f of degree nd>0. The new calculation c^k=u f^k/h^(nd), with u=b^(2n alpha)/a^(2n beta) a degree-zero unit, is written explicitly in the step. Both u and its inverse exist in A_h, so the chart-intersection lemma applies even with zero divisors. This proves the coefficient unit locus; equality on a covering gives equality of sets without a gluing existence theorem.

Step 3 cites `lem-weil-pbc-proj-standard-open-inclusion` only for its positive-degree homogeneous basis clause, which its statement contains. I checked that U open in P makes an open neighbourhood N in U also open in P; thus the chosen D_+(g) lies in U, not just its intersection. Taking f=g^d makes its degree qd positive and divisible by d, and primality proves D_+(g^d)=D_+(g). This establishes the basis directly and uses no quasi-compactness. Step 4 cites `def-pc-proj`: its statement identifies each positive-degree standard open as the affine scheme Spec(A_(g)). It therefore says exactly what is needed for the particular opens constructed in Step 3. The affine members refine every neighbourhood, proving the affine-open basis assertion. These off-unit tools are generic definitions/topology and are declared in split_report where required, with no replacement of the unit route.

For B--E: there are no new node form, duplicate or Mathlib-leaf obligations; the item has a complete proof with all non-elementary inputs cited, no restatement child and no circular citation. I verified every citation quote is a literal substring of the cited statement. Each step is shorter than 2000 characters. I checked the empty open U (all pointwise and basis conditions vacuous), f=0 or nilpotent (empty standard open and empty nonvanishing locus), d=1 (the power refinement is unchanged), a or b=0 (empty chart), beta=0 (all fractions and the unit u still have the asserted degrees), and nonreduced rings (only fraction identities and local-ring unit criteria are used). No Noetherian, quasi-compactness, reducedness, domain or degree-one-generation hypothesis was added. The corrected affine refinement and eliminated elementary child were the substantive self-review repairs.

## What remains

No unresolved mathematical or source issue. Delivery checks are run separately by the required server tool; no Lean file, compiler, Lake command, live-project write or source-checkout write is involved.
