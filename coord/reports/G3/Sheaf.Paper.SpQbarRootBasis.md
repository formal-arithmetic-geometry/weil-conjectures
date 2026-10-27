## What changed

Added the proof import `Sheaf.Paper.SpQbarPositiveRootBasis`. The assigned
degree-one theorem now specializes its positive-degree companion at `d = 0`.
Added the new statement module and its DAG node. The companion theorem retains
one named `sorry` for the positive-degree root-tower construction, which is the
strictly lower positive-power step of the argument.

## Proved and sorry left

Closed the original `AlgebraicGeometry.ProEtale.spQbarRootBasis` hole.
The proof is the real specialization `spQbarPositiveRootBasis ... 0`.

One sorry remains, in `AlgebraicGeometry.ProEtale.spQbarPositiveRootBasis`,
attached to `lem-sp-qbar-positive-root-basis`. It states the positive signed
power construction needed before the degree-one specialization. No definition
contains a sorry.

## No longer needed

No original proof-dependency import was removed. The new module imports only
`Sheaf.Paper.ProEtaleTateTwistConstructions`; no additional stated dependency
was needed for the specialization.

## Where the brief, the DAG or earlier work was wrong

The original item presents the degree-one colimit construction as one monolithic
statement. The finite-level and colimit argument naturally first yields the
positive signed-power statement, so this delivery records that lower step as a
separate node and specializes it for degree one. No target statement or unit
route was changed.

## New nodes

`lem-sp-qbar-positive-root-basis` is the positive-degree companion theorem in
`lean/Sheaf/Paper/SpQbarPositiveRootBasis.lean`. Its source and proof plan are
recorded in the node file.

## Second reading by G3

Pending independent review. The specialization preserves the exact target
statement; the new node is a positive-degree intermediate statement with the
same root-tower data and a strictly broader positive-degree conclusion.
