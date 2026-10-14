## What changed

In `Sheaf.RingTheory.ProjectiveResolutionExtDegree`, simplified the forward direction of
`ModuleCat.projective_resolution_ext_degree` to apply Mathlib's
`HasProjectiveDimensionLT.mk` directly, rather than passing through the equivalent
`hasProjectiveDimensionLT_iff`. The degree equality supplied to `extMk_surjective`
already used `rfl` in the repository version and is unchanged.

The declaration's signature, visibility, docstring, imports, and reverse construction
are unchanged. Updated the existing node's proof and proof_origin to match the proof.
The module compiles cleanly through `lcompile.py`.

## Proved and sorry left

`ModuleCat.projective_resolution_ext_degree` is completely proved. The checked-in
module already contained zero sorries when this worker started. Holes closed: none
(0 of 0). Holes added: none. Sorries left in the delivered module: none. This is a
small proof simplification and verification of an already-completed queued repair,
not a new proof or decomposition and not net sorry progress.

## No longer needed

None. No imports, nodes, or modules are pruned. The reverse direction still needs
`Sheaf.RingTheory.ProjectiveResolutionSuccSplice`, and the forward direction needs
Mathlib's resolution Ext API. The bounded-resolution definition and Mathlib dimension
API remain necessary. No unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The dispatch brief says this module still contains `sorry`, but the supplied repository
version already has a complete proof and compiles cleanly. The item remains listed in
`coord/repairs.txt` for upstream review #1428. Its current statement is the repaired
explicit-bounded-resolution/Mathlib-dimension bridge, not a duplicate statement of
Mathlib's Ext-vanishing criterion: one side quantifies over actual projective resolutions.
The existing proof correctly reuses Mathlib's Ext criterion, projectivity criterion,
and dimension shifting, and the already proved successor-splicing construction.
No statement correction, definition change, forced adaptation, or new node is needed.


## Second reading by J2

1. **Interface: pass.** Compared the delivered module with the repository using
   `diff -u`. The only changed Lean line replaces
   `rw [HasProjectiveDimensionLE, hasProjectiveDimensionLT_iff]` by
   `apply HasProjectiveDimensionLT.mk`. The existing theorem signature, universes,
   visibility, docstring, definitions used by its statement, and imports are byte for
   byte unchanged. No change record or forced adaptation is needed.
2. **Proof: pass.** Read the entire proof and the definitions of both predicates,
   Mathlib's dimension constructor and shifting lemma, and the successor-splicing
   theorem. Compiled the delivered file with `lcompile.py`: no errors or warnings.
   Compiled a scratch copy with `#print axioms ModuleCat.projective_resolution_ext_degree`:
   exactly `propext`, `Classical.choice`, and `Quot.sound`. There are no local sorries,
   forbidden declarations, new definitions, or arbitrary choices from unproved existence.
   The forward direction uses `n + 1 ≤ i` to obtain `n < i`, kills the representing
   cocycle from the zero source, and applies `extMk_zero`. The reverse direction uses
   a projective self-resolution at zero and the kernel of `Projective.π X` at a
   successor; dimension shifting gives precisely the bound required by induction,
   and the existing splice constructs the required bounded resolution.
3. **Split statements: pass, none.** No new theorem, new node, or split-off sorry.
   The zero-bound case is explicitly proved; for a zero module the same construction
   applies without any nonzero assumption. No finite-generation hypothesis is used.
4. **Route and pruning: pass.** Searched the local Mathlib projective API and both
   library RingTheory directories by the explicit-resolution predicate and bounded
   resolution terminology. Mathlib supplies the dimension constructor, zero-bound
   projectivity criterion, and dimension shifting already used here; it does not
   supply the library-specific explicit-resolution bridge. Read GlobalDimension and
   ProjectiveResolutionSuccSplice. Both public imports supply the statement's predicates;
   both plain imports supply proof APIs. No old proof dependency is discarded, so
   `No longer needed: None` is complete. Read `dag/units/sk-thm-p1.json`, including
   `realized`: no unit statement or realized step is bypassed by this constructor edit.
5. **DAG: pass.** Compared the old and delivered node. Only `proof` and `proof_origin`
   change; the statement, Lean attachment, and dependency list remain unchanged.
   The four proof steps match the cocycle argument, projective zero case, kernel
   dimension shift, and the existing successor splice. Their cited dependencies have
   the declarations actually used (`Abelian.Ext`, the explicit bounded-resolution
   definition, and `hasProjectiveResolutionLE_of_shortExact_projective_middle`).

Second reading changed only the report and the node's proof_origin: removed the
incorrect claim that J2 changed `omega` to `rfl`, since the baseline already used
`rfl`. The Lean proof needed no repair. Holes closed: none (0 of 0); holes added:
none; split off: none. This delivery verifies and simplifies an already proved repair.
