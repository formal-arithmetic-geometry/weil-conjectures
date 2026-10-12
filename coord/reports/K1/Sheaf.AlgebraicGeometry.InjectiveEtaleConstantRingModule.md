## What changed

Proved `AlgebraicGeometry.Scheme.exists_injective_etale_ring_module` with its original
signature. Added the proof-only import `Sheaf.AlgebraicGeometry.EtaleConstantRingModuleEquivalence`.
The new module constructs scalar extension and restriction, proves their unit and counit
isomorphisms, and proves the equivalence. All data definitions are explicit and use Mathlib's
`PresheafOfModules.sheafify`; no postponed proof supplies data.
The requested theorem uses `Equivalence.map_injective_iff` and the definitional identity of
underlying abelian presheaves. Updated the item's proof route and dependencies accordingly.
No existing statement, definition, public import, or target signature changed.

## Proved and sorry left

Proved the item's sole sorry, `AlgebraicGeometry.Scheme.exists_injective_etale_ring_module`.
Also proved `AlgebraicGeometry.Scheme.etaleConstantModuleFunctor_isEquivalence` and
`AlgebraicGeometry.Scheme.etaleConstantModuleCounitHom_underlying`, with explicit constructions
of both functors and their inverse isomorphisms. No sorry remains in either delivered module.
The construction permits the zero ring and the empty scheme and uses the original universe.
Local compilation succeeded; the required delivery dry run supplies the final checks.

## No longer needed

No import was removed from the original module: its three public imports support its unchanged
statement. The new proof does not import or use
`Sheaf.Paper.SiteSheafificationSectionsLocal` (node
`lem-weil-pbc-site-sheafification-sections-local`) or the separate statement
`lem-weil-pbc-ring-sheafification-underlying-sets`.
Mathlib's locally bijective ring-sheafification unit and module-sheafification construction
supply the needed local action and its universal property directly.
The `Sheaf.AlgebraicGeometry.EtaleSheaves` module and its node
`def-weil-pbc-etale-sheaves` are not needed as proof dependencies: this argument uses only
Mathlib's `Sheaf` category, not the locally constant, constructible, or torsion predicates.
The old direct dependencies `def-weil-pbc-constant-sheaf`, `def-weil-pbc-sheafification`,
`def-weil-sheaf-of-modules-category`, and `def-weil-pbc-abelian-etale-sheaves` are now covered
by the proved equivalence node; their definitions remain relevant and are not globally pruned.
The unit sk-thm-p1 and every node in its realized statement and steps are retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement needed correction. The DAG's expanded local-representative route
was unnecessary because Mathlib already implements the local scalar action and its universal
property. Its local-sections declaration also uses small-category precoverage hypotheses,
whereas the present construction works directly on the etale site.
LeanFinder found `PresheafOfModules.sheafify` and its Hom equivalence; Loogle found
`Equivalence.map_injective_iff`; source grep confirmed both APIs. LeanSearch returned
Internal Server Error, recorded as unavailable. The whole blueprint was searched for
constant-ring equivalences; no existing node states this equivalence for all module sheaves.
The ancestor tool reports a null blueprint ancestor for this chain, so the new node records
null and the explicit existing chain, rather than inventing a blueprint ancestor.
The source TeX is not present in this clone. The Stacks pages 093I, 03CV, and 0H7J were read
online; they describe the structures. The equivalence argument is recorded as agent-written
and is fully checked by Lean, not attributed to a nonexistent theorem in those sections.

## New nodes

`lem-weil-pbc-etale-constant-ring-module-equivalence`, at
`dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-constant-ring-module-equivalence.json`,
is the proved equivalence and its explicit data in
`lean/Sheaf/AlgebraicGeometry/EtaleConstantRingModuleEquivalence.lean`.
It isolates steps 1--3 of the original argument and contains no sorry. There are no change records.

## Second reading by K1

1. **Visible changes and statements.** Compared both delivered modules with the repository versions using `diff`. The existing theorem signature is byte-for-byte unchanged; the only changes are the proof-only import, proof terms, and the new equivalence module/node.
2. **Proof checks.** Compiled both modules with `lcompile.py --all`; no errors, warnings, or `sorry` remain. Scratch `#print axioms` checks report only `propext`, `Classical.choice`, and `Quot.sound` for the two principal declarations. No forbidden declarations occur.
3. **Split-off statements.** The equivalence theorem and its supporting declarations are new, mathematically substantive, and do not duplicate an existing library declaration; their node statements and docstrings describe the construction and its strength.
4. **Pruning and route.** The proof uses Mathlib's module sheafification and equivalence APIs directly. The report's no-longer-needed dependencies agree with the code, and the unit `sk-thm-p1` remains realized by the existing route.
5. **DAG agreement.** The item and equivalence nodes record the declarations, proof steps, dependencies, origins, and module paths used by the compiled proofs; no target or definition was altered.

I changed only this second-reading report section after review; no Lean source or DAG statement required repair.
