## What changed

Completed `AlgebraicGeometry.symmetricProduct_finite_surjective_of_isNoetherian` in
`Sheaf.AlgebraicGeometry.NoetherianSymmetricProductFiniteSurjective`, preserving its entire
signature. Apply the first conclusion of `symmetricProduct_finite` to the chosen coefficient
morphism, and eliminate the two existential witnesses of `symmetricProduct_surjective`.
Their invertibility and epimorphism witnesses are proofs, so proof irrelevance identifies
the morphisms without unfolding the construction. The Noetherian assumption is retained.

The file compiles cleanly through `lcompile.py` (4.2 seconds). Both imports are acyclic.
Read the item node, both dependency nodes and their recorded and superseded Lean declarations,
the properties declaration, the unit record, the current blueprint statement and proof,
and Stacks `etale-cohomology.tex`, `lemma-reduce-to-P1`, final paragraph. The unit record
has no realized proof steps to bypass. No statement, definition, visibility or public import
changed.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.symmetricProduct_finite_surjective_of_isNoetherian`
(node `lem-fin-symmetric-product-finite`). Added zero holes, split off zero statements,
and left zero holes in the item module.

This is a proof from existing declared lemmas, as requested at stage 3. It still depends on
the existing holes `AlgebraicGeometry.symmetricProduct_finite`,
`AlgebraicGeometry.symmetricProduct_surjective`, and the properties/construction results
already used in the signature. This delivery does not claim to discharge those dependencies.

## No longer needed

Removed the unused proof import
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.SymmetricProduct`.
Its recursive tower construction is not used in this proof. The two declared coefficient
lemmas give the statement immediately without a comparison of constructions.

No declared proof dependency is pruned: both `lem-weil-pbc-symmetric-product-finite`
and `lem-weil-pbc-symmetric-product-surjective` are used through their original coefficient
formulations. No new module or node is needed.

## Where the brief, the DAG or earlier work was wrong

The two dependency nodes were repointed on 2026-10-17 to the source library's proved
recursive-tower morphism. Those declarations do not directly accept this module's arbitrary
limiting product cone and coefficient-section morphism. Their still-existing superseded
Sheaf declarations have exactly the interfaces used by the item's documented proof, so
this delivery uses them. A future replacement by the recursive results needs an identification
of the two constructions, not just the repointed node record.

Searches run: LeanFinder for the finite surjective coefficient morphism, Loogle for
`"symmetric", "finite"`, msearch grep for symmetric-product finiteness/surjectivity,
and local `rg` over both library roots. The source recursive results were read; no shorter
applicable statement than the existing coefficient declarations was found.

The first elaboration with `obtain` exhausted Lean's 200000 heartbeats. Direct existential
elimination compiles at the default heartbeat limit; no definition or limit was changed.

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
