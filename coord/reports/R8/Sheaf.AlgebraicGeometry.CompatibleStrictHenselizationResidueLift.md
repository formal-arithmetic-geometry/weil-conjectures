## What changed

Retire the zero-hole duplicate
`Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationResidueLift`, as listed in
`coord/retire-items.tsv`. Point its existing DAG node
`lem-weil-pbc-compatible-strict-henselization-residue-lift` at the complete adopted
`WeilConjectures` theorem with the same declaration name. Update the proof plan
and proof dependencies to match that theorem's actual affine-chart argument.

Change record:
`coord/changes/R8-retire-compatible-strict-henselization-residue-lift.md`.
No source-library file changes. No target or unit statement changes.

## Proved and sorry left

The assigned module has 0 holes before and 0 after. Holes closed: none. Holes
added: none. Split off: none. This is duplicate retirement, not a new hole closure.
The retained `AlgebraicGeometry.Etale.exists_compatibleStrictHenselizationResidueLift`
already has a complete proof. The original small-model statement is also checked
by a scratch Lean proof transporting both spectrum isomorphisms through the
canonical colimit comparison over the base.

Validation: unchanged copies of the adopted lift theorem, its residue-square
caller, and the structural comparison module compiled with lcompile.py. The
scratch transport proof compiled (8.5 seconds), as did the exact withdrawal
stub (0.4 seconds). The retained lift theorem, the residue-square caller, the
comparison theorem, and the transport proof all print exactly `propext`,
`Classical.choice`, and `Quot.sound`; no `sorryAx` occurs.

## No longer needed

Pruned module: `Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationResidueLift`.
All four imports disappear with the duplicate. Its upstream counterpart retains
the required henselian and ind-etale arguments. In particular,
`Sheaf.AlgebraicGeometry.SmallStrictHenselizationIndEtale` is no longer a direct
proof dependency of this node; the retained theorem uses
`lem-weil-pbc-strict-henselization-affine-chart-ind-etale` instead.
The small-model bridge and structural-map modules still have other users and
are not withdrawn. The raw local-ring triples and strict-henselization triples
results remain indirect dependencies of the affine-chart proof.

There are no current Lean importers, including in quarantine. The only incoming
DAG dependency is `compatible-strict-henselization-residue-square`. Its Lean
attachment is already the upstream parent, which directly imports and calls the
retained upstream theorem. No unfinished or quarantined parent is disconnected.
All node identities and the `sk-thm-p1` route remain intact.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an obligation still containing a proof hole;
the current assignment is a listed zero-hole retirement. The initial comparison
marked the upstream signature DIFFERENT because of the two strict-localization
presentations. They are canonically isomorphic over the base. A compiled transport
proof checks the entire original signature, including its specified residue map.
The old node's proof steps cited triples directly while its proof dependencies
listed the small-model chart bridge; the updated plan follows the retained full-model
proof instead.

Searches via msearch.py found residue-field APIs but no shorter Mathlib theorem;
the existing adopted theorem is the exact reusable result after model transport.

## Second reading by R8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
