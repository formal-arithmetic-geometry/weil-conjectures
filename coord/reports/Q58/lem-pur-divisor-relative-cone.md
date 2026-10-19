1. Files written: `dag/nodes/sec-smooth-purity/lem-pur-divisor-relative-cone.json` (statement, no new child nodes; Mathlib searches found only general mapping-cone APIs); `citations.json`; this report.

2. Attachments: none.

3. WANTED: none.

4. The imported item had an empty proof and stale creation metadata from an earlier group. I retained its statement and dependency list, corrected the creation metadata for Q58, and supplied the missing resolution, cone, support, boundary, naturality, and site-comparison arguments. No statement correction was required. The direct cone calculation uses degreewise surjectivity of restriction for injective sheaves; the comparison step uses the existing arbitrary-abelian-sheaf etale–pro-etale comparison. No SGA source is used.

5. Nothing remains unfinished. There are no new nodes and hence no duplicate-node pair to report.

## Review by Q58

I read the item, its unit `sk-prop-a1-kummer`, chapter `sec-smooth-purity`, and the cited blueprint proof `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/lem-pur-divisor-class.proof.md`. The item statement matches the imported support-boundary and ordinary-cohomology-comparison clauses, including both site choices, the sign in the differential, the coefficient and restriction compatibilities, and the final pro-etale coefficient morphism clause.

Step 1 uses the statement of `lem-weil-pbc-injective-sheaf-mono-restriction` exactly for the monomorphism represented by the open complement, and the injective-resolution definition to obtain the two section complexes. I checked that the kernel is degreewise `K` and that the differentials preserve it. Step 2 uses the signed cone definition and the abstract cone convention. I checked the lift of a degree-`q−1` element of `B` and the resulting replacement of a cycle `(a,b)` by `(a−dx,0)`; the same calculation on boundaries proves the quasi-isomorphism, including the negative-degree zero extension.

Step 3 uses the kernel-of-restriction definition of supported sections, so the cohomology of `K` is precisely the right-derived supported-sections group for the chosen injective resolution. I checked that the first cone projection is the forgetting-support map and that the cone projection sign gives `b ↦ (0,−b)`. The cited cone definition also supplies functorial maps for coefficient morphisms and commuting restriction squares, which covers etale neighbourhoods and enlargements of support.

Step 4 uses the existing comparison theorem for arbitrary abelian etale sheaves separately on `T` and `W`; I checked that inverse-image naturality makes their square commute with restriction. The induced map of signed cones is therefore an isomorphism on cohomology by the long exact cone sequences and five lemma. Its naturality gives all listed compatibilities, and postcomposition gives the final assertion for a pro-etale coefficient morphism. The small edge cases `Z=∅`, `Z=T`, `F=0`, and `q=0` reduce to the same kernel and cone formulas.
