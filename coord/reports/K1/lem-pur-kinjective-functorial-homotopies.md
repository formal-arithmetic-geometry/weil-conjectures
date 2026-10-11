# Stage 1 report

1. Files written:

- `dag/nodes/sec-smooth-purity/lem-pur-kinjective-functorial-homotopies.json`, split into three proof steps.
- `dag/nodes/sec-smooth-purity/lem-pur-kinjective-cone-contractible.json`, Mathlib leaf for `CochainComplex.mappingCone.homotopyToZeroOfId`.
- `citations.json`, verbatim statement quotes for every cited node in every step.

2. Attachments: none.

3. WANTED: none.

4. The item has no sorry-free declaration in `WeilConjectures/`. The existing generic K-injective functorial-existence nodes do not state the pushout construction or its null-homotopy property. I searched the DAG for cone, contractibility, pushout, and acyclic-cokernel statements. The existing contractible-complex node is restricted to chain complexes of modules, so it cannot replace the arbitrary Grothendieck abelian category fact; the new cone node is the exact general Mathlib declaration.

## Not duplicates

lem-pur-kinjective-cone-contractible vs lem-weil-pbc-contractible-complex-acyclic: the new node states the general cochain-complex mapping-cone contracting homotopy in any preadditive category with binary biproducts, while the existing node states that a contracting homotopy implies exactness for chain complexes of modules indexed by the natural numbers.

## Review by K1

I read Stacks `injectives.tex`, Lemma `lemma-functorial-homotopies` (the construction at lines 1705--1741), and checked the item statement clause by clause: a Grothendieck abelian category, a set of acyclic complexes, a functorial natural map, termwise monomorphism and quasi-isomorphism, and null-homotopy for every indexed map. Step 1 follows the source's choice of the cone on each identity. The new Mathlib leaf states verbatim that the identity of this cone is homotopic to zero; together with the cochain, acyclic, and homotopy definitions cited in the step, this gives the required contractible acyclic target and null-homotopic inclusion. Step 2 follows the displayed coproduct pushout in the source. The Grothendieck statement supplies small colimits, while the cochain-complex statement supplies the ambient abelian category and morphisms, so the pushout and its functorial universal map are defined. Step 3 spells out the source's final paragraph: pushout preserves the termwise monomorphism, the quotient is the coproduct of the cone cokernels, short exact cohomology and exact coproducts make this quotient acyclic, and hence the map is a quasi-isomorphism; the chosen cone maps make every composite null-homotopic. I checked that every non-elementary fact named in these steps is represented by a cited node and that each `citations.json` quote is copied verbatim from that node's statement. I tested the construction on the empty index set (the functor is the identity), on a singleton set with the zero complex, and on a singleton set with one acyclic complex. Mathlib searches for the new node used LeanFinder, Loogle, grep, and LeanSearch; the first three found the exact declaration and LeanSearch was unavailable, recorded as such.
## Second reading by K1

- Item statement: checked against Stacks `injectives.tex`, Lemma `lemma-functorial-homotopies` (lines 1704--1717); all hypotheses and both conclusions match. The empty index set gives the identity construction; singleton zero and singleton acyclic complexes satisfy the stated cone and null-homotopy clauses.
- Step 1: checked against the source cone construction (lines 1720--1723) and Mathlib `CochainComplex.mappingCone.homotopyToZeroOfId`, line 93; the inclusion and its null-homotopy are correctly obtained from the contracting homotopy.
- Step 2: checked against the displayed pushout diagram and functoriality paragraph (lines 1724--1734); the summand indexing, action on morphisms, and use of small colimits are now explicit.
- Step 3: checked against the source final paragraph (lines 1735--1741); the abelian cokernel presentation proves pushout monicity, followed by the cokernel coproduct calculation, acyclicity of each cokernel, exactness of coproducts, the quasi-isomorphism conclusion, and null-homotopy factorization.
- New node `lem-pur-kinjective-cone-contractible`: checked against the exact Mathlib declaration and retained as a Mathlib leaf; it is strictly smaller than the item and is not duplicated by the existing module-specific contractibility node.

Changes: expanded steps 2 and 3 to replace compressed claims with their constructions; corrected the Grothendieck citations to quote the complete definition; kept pushout monicity within the item's abelian cokernel calculation to avoid a cross-unit tool dependency; recorded the source and small-case checks above. No node was removed.
