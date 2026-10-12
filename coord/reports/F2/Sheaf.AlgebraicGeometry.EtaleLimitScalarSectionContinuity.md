## What changed

Added two strictly smaller helper modules splitting the representative and eventual-zero conjuncts, each with a named theorem, and proved the parent theorem by introducing its lets and hypotheses and combining the two helper results. The parent imports the helper modules.

## Proved and sorry left

The parent theorem `AlgebraicGeometry.Etale.etale_limit_scalar_sections_representatives_and_zero` is proved by conjunction. The helper declarations `AlgebraicGeometry.Etale.etale_limit_scalar_sections_representatives` and `AlgebraicGeometry.Etale.etale_limit_scalar_sections_zero_eventually` remain `sorry`, each recorded by its new node; this is a strict two-conjunct decomposition.

## No longer needed

None; the parent still retains its planned imports and the helper modules use the same affine-site declarations.

## Where the brief, the DAG or earlier work was wrong

The original node treated the two independent filtered-colimit conclusions as one indivisible hole. They are separated here into the two conjunct statements so each can be proved independently.

## New nodes

`lem-weil-pbc-etale-limit-scalar-section-representatives` and `lem-weil-pbc-etale-limit-scalar-section-zero-eventually` record the two helper declarations and their sources.

## Earlier second reading (a previous round; superseded)

The parent proof is a direct conjunction of the two strictly smaller helper statements. Both helper statements retain the exact corresponding conjunct and the source hypotheses; their remaining proofs are explicitly staged for the next reader.

## Second reading by F2

1. **No accidental visible changes.** Compared the delivered parent module with the repository version: the theorem signature is byte-for-byte unchanged; only its proof and two helper imports were added. The two helper modules are new declarations recorded by the two new DAG nodes.

2. **Compilation and axioms.** Compiled all three sandbox modules with `lcompile.py --all`; they compile cleanly. The parent has no `sorry`, while the two helper theorems retain the named `sorry`s listed above. No definitions contain `sorry`, and no forbidden declarations were added. The helper `sorry`s are the explicit staged holes represented by their nodes.

3. **Statements and split nodes.** The helper statements are exactly the first and second conjuncts of the parent, with the same hypotheses and maps, so each is true whenever the parent statement is true and is strictly smaller than the conjunction. Their source, proof descriptions, declarations, and `proof_deps` agree with the Lean files; no existing Mathlib or library declaration duplicates either name.

4. **Pruning and route.** The parent proof follows the unit route by reducing to the two conjuncts and does not alter the unit statement or definitions. The original imports remain because the parent and helper signatures mention the affine-site, sheaf, and limit constructions they provide; no import was removed. The parent node now records both helper nodes as proof dependencies.

5. **Unit and DAG agreement.** The unit `sk-thm-p1` remains realized by the original parent node. The parent proof is the conjunction of the two helper declarations exactly as written, and each helper node records its module, declaration, statement, source, and proof route. Verdict: the delivered proof proves the unchanged parent statement, with the two explicitly staged conjunct holes left open.

No further changes were required during second reading.
