## What changed

Withdrew `Sheaf.Paper.EtaleProEtaleCubeFlatModel` under brief step 8d. The complete,
already-landed replacement argument is included in
`Sheaf.Paper.EtaleProEtaleScalarPullbackCube`: ordinary restriction coherence passes
through exact localization, conjugation to left-derived pullbacks, and mate pasting;
cancelling the reverse scalar comparisons gives the stated parent cube directly for
every derived object. The parent proof and signature are unchanged. Its stale docstring
now describes this actual proof, and its node explicitly reconciles the shorter route
with this withdrawal. The withdrawn node remains with lean=null.

The current parent module is unclaimed. No change is made to the source-library tree,
any target, or the scalar-six unit and its etale/pro-etale comparison route.

Change record: coord/changes/J7-etale-proetale-flat-model-withdrawal.md.

## Proved and sorry left

Original item holes: 1, named
`AlgebraicGeometry.ProEtale.ScalarCubeFlatModel.simultaneous_flat_model`.
Holes proved: 0. Holes removed by withdrawal: 1 (that declaration).
Holes added: 0. Split off: 0. Remaining item holes: 0.
The retained parent module has zero sorry tokens, and its unchanged complete proof
compiles through lcompile.py. Imported pre-existing dependencies retain their proofs
and holes; none is replaced by sorry or removed.

## No longer needed

Pruned the module `Sheaf.Paper.EtaleProEtaleCubeFlatModel` and its 18 declarations.
Its node `lem-sfb-etale-proetale-cube-flat-model` is no longer needed by the targets'
mathematical route. Its former parent uses the complete direct mate argument included
in this packet. No imports are removed from any retained module.

Audited every active node's stmt_deps, proof_deps and proof uses: no current edge to the
withdrawn node. The parent node's only old mention is historical reviewer text.
Audited lean/Sheaf, lean/WeilConjectures and quarantine for the module and
ScalarCubeFlatModel namespace: no external consumer. Audited dag/units and dag/chapters:
no reference; sk-prop-scalar-six.realized contains no attachment to this node.
Checked rework.tsv and the current claim/return records: this is a present source module,
not a quarantined assignment, and J7 holds it. Thus withdrawal is based on the actual
replacement argument and all dependency routes, not just the absence of Lean importers.

The withdrawn module's imports are not declared globally unnecessary: retained definitions
and other modules can still need those libraries. No other node or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The dispatched item described an auxiliary common-flat-model step that the parent no
longer needs. The live parent has a proved categorical route, recorded by N1's stage-3
report and its current proof/proof_deps. Its Lean docstring still described the old
resolution argument; that mismatch is corrected here. This delivery claims pruning,
not a new proof of the withdrawn simultaneous-flat-model statement.

Before discovering this route change, I wrote and compiled resolution, naturality,
representative-isomorphism and preservation helpers and drafted all face calculations.
Those drafts are not delivered as library code: proving an unused auxiliary statement
would conflict with the stage's target-downward pruning principle.

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
