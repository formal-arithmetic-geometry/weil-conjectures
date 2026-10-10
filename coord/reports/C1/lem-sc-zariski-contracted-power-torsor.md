# Stage-1 report

1. Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-zariski-contracted-power-torsor.json`: statement split into four proof steps; no new nodes; no Mathlib match.
- `citations.json`: verbatim statement excerpts for every cited node at every step.
- `report.md`: this report.

2. Attachments: none. The slopmaster2 source contains no declaration tagged `lem-sc-zariski-contracted-power-torsor` and no sorry-free declaration with this statement.

3. WANTED: none. The blueprint source is agent-written and is available only through the imported node's source/proof description; the construction is explicitly not attributed to Stacks 02FQ.

4. What was checked and corrected: the item statement was retained exactly. The existing DAG was searched for the contracted-product and integer-power facts; `lem-sc-torsor-h1` is the existing statement for the contracted product, so no duplicate supporting node was created. The proof now has four steps: local triviality and induction for powers; concatenation and cancellation for `mu`; direct representative checks for associativity, commutativity, and units; and the explicit inverse pairing. The proof uses only `def-sc-gm-torsor` and `lem-sc-torsor-h1`, whose statements were read and quoted in `citations.json`. The small cases `n=0`, `n=1`, and `m=1,n=-1` were checked directly; the trivial torsor gives the usual integer grading. Mathlib searches were run with LeanFinder, Loogle, grep, and LeanSearch; no matching declaration was found (LeanSearch was unavailable).

## Review by C1

I read the imported item and its ancestor blueprint description, plus the statements of `def-sc-gm-torsor` and `lem-sc-torsor-h1`. Step 1 uses the definition's local free-transitive action and the existing contracted-product operation; the induction is the same local trivialization argument for each finite string of factors. Step 2 uses those same statements for the quotient and action, and spells out the cancellation that supplies the canonical map and degree-zero constraints. Step 3 is the elementary representative calculation: concatenating three strings is associative, swapping strings is valid because G is abelian, and the empty string gives units. Step 4 uses freeness/transitivity to define the unique difference h and the contracted-product relation for the inverse pairing. I checked that every quote in `citations.json` is a verbatim part of the cited statement, that all hypotheses (abelian G, local torsor sections, and restriction compatibility) are in force, and that no step cites a node for facts its statement does not provide. The edge cases n=0, n=1, and the trivial torsor were checked; no statement or dependency was changed.

5. What could not be finished: none.

## Second reading by C1

- Item statement: checked against its unsplit DAG statement, the cited torsor and contracted-product statements, and Stacks 02FQ (which proves the torsor/H1 correspondence by a different construction); verdict: unchanged, including the degree-zero, one-factor, inverse, and empty-scheme cases.
- Step 1: checked against `def-sc-gm-torsor` and the antidiagonal product in `lem-sc-torsor-h1`; verdict: the local coordinate sum proves every signed power is a torsor.
- Step 2: checked against those same statements and the transition t_1=c\cdot t_0; verdict: the degree-k coordinate shifts by -kc, so the addition maps glue for every pair of integers.
- Step 3: checked against the abelian hypothesis and the quotient description in `lem-sc-torsor-h1`; verdict: both associativity composites are a+b+d, symmetry is b+a=a+b, and the zero coordinate gives both units.
- Step 4: checked against freeness and transitivity in `def-sc-gm-torsor`; verdict: h=a+b is invariant under the quotient relation and the proposed inverse class is independent of its local choice.
- New nodes: none; checked existing DAG nodes for the product and inverse construction and searched Mathlib using alternate Picard-groupoid and torsor terminology. Neither search found a sheaf-torsor contracted-power declaration.

Changed the four proof steps to give explicit coordinate formulas and overlap, coherence, and inverse checks. The first worker's citations still quote the statements used by each step, so `citations.json` needed no change.
