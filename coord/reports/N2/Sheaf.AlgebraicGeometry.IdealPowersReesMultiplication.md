## What changed

Added `Sheaf.AlgebraicGeometry.IdealPowersReesMultiplicationComponent`, whose componentwise
existence theorem is the affine multiplication and gluing step. The target module now obtains
all maps by dependent choice and proves the original simultaneous existence statement. The new
proof-only import is `Sheaf.AlgebraicGeometry.IdealPowersReesMultiplicationComponent`.

## Proved and sorry left

`AlgebraicGeometry.idealPowersReesMultiplication` is proved from the component theorem.
`AlgebraicGeometry.idealPowersReesMultiplication_component` remains `sorry` (node
`lem-weil-pbc-ideal-powers-rees-multiplication-component`).

## No longer needed

Removed the proof-only imports `Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`
and `Sheaf.AlgebraicGeometry.ModulePullbackIdealQuotient`; the target proof now uses only the
component theorem. Their corresponding proof-dependency nodes are no longer used by the target.

## Where the brief, the DAG or earlier work was wrong

The original node's affine gluing argument is not yet available as a library theorem; it is split
into the strictly componentwise intermediate statement above.

## New nodes

`lem-weil-pbc-ideal-powers-rees-multiplication-component` records the componentwise affine
multiplication/gluing theorem and its source.

## Second reading by N2

1. Compared the delivered target module with the repository version. The theorem signature and
   all existing declarations are byte-for-byte unchanged; only the proof and proof-only imports
   differ. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py`. The target has no local `sorry`; the only
   remaining hole is the explicitly named component theorem, with its node and source docstring.
   Verdict: pass.
3. Checked the component statement against the displayed target formula and tested the dependent
   choice assembly in the compiler. It is strictly per `(m,k,b)` and preserves the exact formula.
   No duplicate library declaration was found. Verdict: pass.
4. The proof uses the component theorem as the shortest available route. The two former proof-only
   imports and their dependency nodes are pruned; the unit route remains realized through the
   component node. Verdict: pass.
5. The target node proof and `proof_deps` match the Lean proof, and the new component node records
   its statement, source, searches, and Lean declaration. Verdict: pass.

Changed the target proof imports and added this second-reading record; no statement or definition
was changed.

## Earlier second reading (a previous round; superseded)

A second worker should compile both modules and check that dependent choice preserves the exact
pointwise formula and that the new component statement is strictly per-index.
