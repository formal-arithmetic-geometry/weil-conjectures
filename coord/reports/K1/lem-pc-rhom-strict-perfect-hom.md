Files written:

- `lem-pc-rhom-strict-perfect-hom.json`: statement split, no new nodes; Mathlib searches found no exact sheaf-valued RHom theorem.
- `citations.json`: verbatim citations for all proof-step dependencies.

Attachments: none.

WANTED: none.

The source declaration search under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` found no declaration tagged `(blueprint: lem-pc-rhom-strict-perfect-hom)` and no sorry-free declaration matching the item. The existing node `lem-sc-finite-free-internal-hom-exact` was checked before use; it gives exactness of internal Hom from a finite free sheaf. The split does not create a node for the bounded finite-projective calculation because it is the item's local proof step: boundedness gives finitely many terms, finite projectives are locally direct summands of finite free modules, and exactness plus direct summands gives acyclicity.

## Not duplicates

`lem-pc-rhom-strict-perfect-hom` vs `lem-sc-finite-free-internal-hom-exact`: the existing node concerns one finite free sheaf and a short exact sequence; this item concerns a bounded strictly perfect complex and derived internal Hom for every complex.

## Review by K1

I read the item's source entry for Stacks Tag 08DM and the definitions cited by the statement. Step 1 uses the derived internal-Hom definition's functorial K-injective resolution and its representative formula. Step 2 uses the statement of `lem-sc-finite-free-internal-hom-exact` exactly for the finite-free local pieces, together with the strictly perfect definition's bounded direct-summand condition and the Hom-complex definition; the cone of a K-injective resolution is acyclic, and the finite bounded direct-summand calculation makes its Hom complex acyclic. Step 3 uses the functorial/well-defined derived-Hom construction to identify the ordinary Hom complex with the derived representative and obtain the canonical comparison.

I checked the hypotheses locally: U is affine as required by the item, P is bounded with finite-projective terms, and only finitely many local finite-free summands occur. The zero-term and one-term cases reduce to the finite-free exactness statement, and a direct summand of an acyclic complex remains acyclic in the abelian sheaf category. The Mathlib searches were run with LeanFinder, Loogle, and Mathlib grep; they found only generic K-projective/HomotopyCategory declarations, not this sheaf-level statement.

Nothing was corrected in the imported statement or blueprint metadata; the proof and citations were added, with no new DAG node.

## Second reading by K1

- Step 1: checked against Stacks Tag 08DM and `def-pur-derived-internal-hom`; the K-injective representative is stated and cited correctly. Verdict: pass.
- Step 2: checked against Tag 08DM's finite-projective calculation and the statements of `lem-sc-finite-free-internal-hom-exact`, `def-pur-hom-complex`, `def-pc-perfect-complex`, and `def-pc-quasi-iso-modules`; the bounded filtration and direct-summand exactness now supply the acyclicity argument. Verdict: repaired and pass.
- Step 3: checked against Tag 08DM's conclusion and the functorial/well-defined clauses of `def-pur-derived-internal-hom`; canonicity and representative independence are now explicit, and the step is correctly non-elementary. Verdict: repaired and pass.
- New nodes: none; the existing finite-free internal-Hom node was searched and used, so no duplicate or Mathlib leaf was created. Verdict: pass.
- Small cases checked: zero complex, one-term finite projective complex, rank-zero free summand, and the zero/field ringed-site cases all reduce to the cited exactness and finite filtration.

Changes made: repaired Step 2 to justify acyclicity via a finite filtration whose graded pieces are exact Hom complexes from direct summand finite-projective terms; repaired Step 3 to state the canonical natural comparison and removed its incorrect `elementary` marker. No statement or blueprint metadata was changed.
