1. Files written:

- `dag/nodes/sec-picard-framework/lem-sc-p1-ext-locally-free-naturality.json`: split statement, no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-ext-evaluation-first-naturality.json`: new unsplit statement, no Mathlib match.

2. Attachments: none.

3. WANTED: none.

4. The imported item had no proof steps. I kept its statement and added the missing first-variable evaluation square as a strictly smaller node. The proof now separates the evaluation square, derived Ext/cohomology transport, the standard-cover multiplication calculation, and the monomial-basis specialization. The Mathlib searches found no exact declarations for the new naturality statement.

5. What I could not finish: no Lean code is written at stage 1; the new statement remains unsplit as required.

## Review by J1

I read the item, the Serre-duality unit record, the chapter record, the existing `lem-sc-ext-locally-free`, `lem-sc-ext-evaluation`, `def-sc-p1-standard`, and `lem-sc-p1-monomial` statements, and the imported blueprint proof text cited by the item. Step 1 cites the new evaluation statement verbatim: it states exactly that $u^\\vee\\otimes1$ corresponds to precomposition. Step 2 cites the existing Ext/cohomology isomorphism statement and the same evaluation square; the derived-functor transport is the standard functoriality used to compare the two canonical constructions. Step 3 uses the standard-cover transition data and the Ext identification; with $u=s$, the dual map is multiplication by $s$, so the induced Cech map is componentwise multiplication. Step 4 cites the monomial node's explicit $\\omega\\cong\\mathcal O(-2)$ and basis clauses and the Ext identification. I checked the new node is self-contained, strictly smaller than the item, has all statement dependencies, and has LeanSearch, Loogle, and source-grep records. I also checked the citation quotes against the exact node statements and tested the specialization at $d=0$ and $d=-1$: the claimed multiplication map and the listed vanishing/basis ranges agree.
