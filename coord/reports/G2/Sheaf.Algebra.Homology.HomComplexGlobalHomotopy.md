## What changed

Proved `CategoryTheory.homComplex_global_homotopy` with its signature unchanged.
Private proved helpers construct the global-complex isomorphism, its naturality,
the external pre/postcomposition cochain map, the zero-degree homotopy-class
comparison, and its homology naturality via `ShortComplex.LeftHomologyMapData`.
The component isomorphisms assemble by `NatIso.ofComponents` and the functor
associator. No data are chosen from new existence statements.

The proof-only import `Sheaf.Algebra.Homology.HomComplexGlobalCochains` was replaced
by `Sheaf.Algebra.Homology.NormalizedHomComplexGlobalCochains`, which supplies the
explicit projection-normalized comparison needed for naturality. The existing
node's proof and dependency fields now record this route. All public imports and
existing signatures are unchanged. A local heartbeat allowance of 400000 permits
the final assembly to elaborate; the single-file compile remains below 60 seconds.

## Proved and sorry left

Closed the one original hole: `CategoryTheory.homComplex_global_homotopy`
(blueprint: `lem-pur-hom-complex-global-homotopy`). All private helpers are proved.
No `sorry` remains in the item and no hole or new module was added.

## No longer needed

Removed proof-only import `Sheaf.Algebra.Homology.HomComplexGlobalCochains`;
node `lem-pur-hom-complex-global-cochains` is not needed by this proof. Its
objectwise existence statement does not retain the projection normalization
required by naturality. The existing explicit comparison from
`lem-pc-normalized-hom-complex-global-cochains` replaces it. No other node or
module in the planned route is pruned; the Hom-complex definition and projection
specification remain necessary.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The planned global-cochain existence theorem is
insufficient on its own to establish naturality of arbitrarily chosen comparison
maps. The library already provides the explicit normalized comparison, so no
new statement is necessary. That proved node is used as a tool from
`sk-thm-picard-duality`; it computes the same global cochains and does not bypass
a unit statement or proof step. The item's unit realization lists are empty.
The argument applies to unbounded and zero complexes without extra hypotheses.

## Second reading by G2

1. Compared the delivered module with the repository version. The public theorem
   signature is byte-for-byte unchanged; the only interface-level import change is
   recorded in the proof route, and no target statement or definition was altered.
   Verdict: pass.
2. Compiled the module with `lcompile.py`; it is error-free and contains no `sorry`,
   `axiom`, `unsafe`, `opaque`, `extern`, or hollow definition. The proof uses only
   the permitted existing assumptions. Verdict: pass.
3. Checked the proof route against the existing normalized global-cochain and
   projection declarations and searched the library for duplicate declarations.
   No new statement was added, and the original theorem is proved unchanged.
   Verdict: pass.
4. Checked pruning and imports: the old objectwise global-cochain existence import
   is unused because the explicit normalized comparison supplies the needed map and
   naturality. The hom-complex and projection imports remain required. Verdict: pass.
5. Compared the node's proof, dependencies, origin, and Lean declaration with the
   proof as written. The dependency replacement and route description agree, and
   the unit realization is unchanged. Verdict: pass.

Changed the proof-only import and synchronized the existing node's proof route and
dependency metadata; no declarations or new nodes were added.
