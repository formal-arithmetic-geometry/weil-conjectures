1. Files written:

   - `dag/nodes/sec-picard-framework/lem-sc-p1-linear-syzygy.json`: item, statement split; no new nodes; existing Mathlib leaf `lem-weil-pbc-polynomial-ring-domain` used.
   - `citations.json`: citations for the two uses of the polynomial-ring domain statement.

2. Attachments: none.

3. WANTED: none. The source path recorded by the imported node is the blueprint proof location; the checked-out repository does not contain the imported blueprint prose file, so the statement and route were checked against the parent node and its reviewed Koszul split.

4. What was wrong or incomplete: the item was unsplit and had no proof. The parent `lem-sc-p1-koszul-resolution` explicitly requires the syzygy calculation at its middle exactness step. I searched the whole DAG, blueprint index, and slopmaster2 source for an existing declaration or duplicate statement and found none. No statement was changed.

5. What I could not finish: nothing.

## Review by F1

I read the item and the parent `lem-sc-p1-graded-resolution`/`lem-sc-p1-koszul-resolution` records, including the parent’s exactness-at-the-middle-term step. The item’s hypotheses are exactly those in the imported statement: a field, `S=k[x_0,x_1]`, and the relation `a x_0+b x_1=0`; its definition dependencies are the existing standard-grading nodes. I also read `lem-weil-pbc-polynomial-ring-domain`: its statement covers polynomial rings over an integral domain, so it applies both to `k[x_1]` in Step 1 and to `S` in Step 2.

Step 1 expands `b` as a polynomial in `x_0`, compares the constant coefficient, and uses the cited domain statement to conclude `b_0=0`; the cited quote is verbatim in `citations.json`. Step 2 substitutes `b=x_0b_1`, factors out `x_0`, and uses the same cited statement for cancellation in `S`; its quote is likewise verbatim. Step 3 is only the elementary sign substitution `c=-b_1`. I checked the edge cases `(a,b)=(0,0)`, `(x_1,-x_0)`, and `(x_1^2,-x_0x_1)`, which give `c=0`, `1`, and `x_1` respectively. The split keeps the parent route and declares the cross-unit domain leaf as a generic tool in `split_report.tool_uses`.
