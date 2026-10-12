## What changed
Added the proof-only import and completed `scheme_iso_derived_inverse_preserves_perfect` by reducing pointwise to the new local transport theorem. Added `Sheaf.AlgebraicGeometry.SchemeIsoPerfectLocalTransport`, whose theorem isolates the local geometric transport step and remains sorry.

## Proved and sorry left
The target theorem `scheme_iso_derived_inverse_preserves_perfect` is proved. The new theorem `scheme_iso_local_perfect_transport` remains `sorry` (node `lem-pc-scheme-iso-perfect-local-transport`).

## No longer needed
None; all original public imports remain needed for the target statement.

## Where the brief, the DAG or earlier work was wrong
The original DAG treated the full local transport argument as a single unformalized step. It is split here into a separately named local theorem so the target proof is complete and the remaining geometric work is isolated.

## New nodes
`lem-pc-scheme-iso-perfect-local-transport`: local strictly perfect model transport under a scheme isomorphism; node file is included in this delivery.

## Earlier second reading (a previous round; superseded)
The target proof unfolds `IsPerfect` and applies the local transport theorem to the image point. The new theorem is strictly local and has the exact data needed by the target; its proof remains open for the next worker.

## Second reading by U2

1. Compared both delivered modules with the repository versions. The existing target theorem signature is byte-for-byte unchanged; the only interface addition is the separately declared local transport theorem, recorded by its node.

2. Compiled both modules in import order with `lcompile.py --all`; compilation succeeds. The target has no `sorry`; the local transport theorem is the sole intentional `sorry`, and it is named and documented with its DAG node. No forbidden declarations or hollow definitions occur.

3. Checked the local transport statement against `IsPerfect` and `IsStrictlyPerfect` definitions and the source description. It is a genuine local reduction, with the exact hypotheses and conclusion needed by the target, and is not a restatement of the target. The target proof applies it pointwise at `s.hom.base x`.

4. The proof follows the unit route by reducing the global predicate to the local transport step. Imports are minimal for the declarations used: `PerfectComplex` is public, `DerivedCategory` and the local transport module are proof/interface dependencies. No old proof dependency is unused.

5. DAG and Lean agree: the target node records the new proof dependency, and `lem-pc-scheme-iso-perfect-local-transport` records the split theorem, statement, source, and proof plan. The unit route remains represented by the target and local node.

Changed only the report during this reading; no proof or statement repair was needed.
