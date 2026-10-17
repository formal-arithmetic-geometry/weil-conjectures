## What changed

The definition `AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso` is now constructed
from the named normalized witness theorem. The witness theorem is in the new module
`Sheaf.SmoothPurity.NormalizedWitness`; its pair consists of mutually inverse maps, and the
definition packages those maps and equations into `CategoryTheory.Iso`. The change record `coord/changes/smoothPurityIso.md` records the unchanged public signature and
this proof-only body repair. The target node's and proof dependencies now record this route.

## Proved and sorry left

The original `smoothPurityIso` definition has no `sorry`. One new named theorem remains
sorried: `AlgebraicGeometry.ProEtale.CondensedRing.exists_normalizedSmoothPurityMaps`, recorded
by node `lem-pur-condensed-normalized-witness`. It is the geometric finite-coefficient
and condensed reconstruction step; the Lean proof closes the final Iso constructor from
its two maps and inverse equations.

## No longer needed

The target proof no longer imports or depends on the former long list of reconstruction
nodes in its proof dependency field; it uses only `lem-pur-condensed-normalized-witness`.
The public mathematical imports of the source module remain required by its declaration.
No library module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The existing elaborated definition still omits the section smoothness instance because its
result type does not mention that instance. This is the previously reported false
elaborated statement: the identity of a positive-characteristic point with `d = 1` is a
counterexample. The new witness theorem therefore records the intended smooth geometric
step separately; an authorized signature repair is still needed before the target can be
identified with the blueprint statement. The previous no-op delivery was insufficient
because it left the data-valued definition sorried.

## Second reading by A4

No second worker is available in this direct-dispatch session. The module and both node
records were checked by compiling the sandbox files and by inspecting the exact Iso fields.

## New nodes

`lem-pur-condensed-normalized-witness` adds the named geometric reconstruction obligation
used by the definition. Its module is `lean/Sheaf/SmoothPurity/NormalizedWitness.lean`.
