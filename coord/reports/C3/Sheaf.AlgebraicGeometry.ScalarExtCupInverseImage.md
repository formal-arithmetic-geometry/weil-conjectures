## What changed

Restored lean/Sheaf/AlgebraicGeometry/ScalarExtCupInverseImage.lean from its
quarantine archive. Replaced its public import of the withdrawn empty
Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations with
WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations, the
canonical module already recorded by the operation node. Preserved the complete
theorem signature and proof verbatim. No upstream source file was modified.

The unmodified archive reproduced the recorded error at line 26: `Unknown
identifier Field` (imported privately). The repaired module compiled cleanly
through lcompile.py in 25.5 seconds. Its proof still expands scalarExtCup,
transports composition, applies the existing second-factor identity, reassociates,
and applies the existing first-factor identity. Both declared dependencies remain
used. The unit route is unchanged.

Change record: coord/changes/scalar-ext-cup-inverse-image-upstream-import-C3.md.

## Proved and sorry left

AlgebraicGeometry.Scheme.Modules.scalarExtCup_inverseImage retains its complete
proof. This is a zero-hole quarantine repair: 0 holes initially, 0 closed, 0 added,
0 split off, and 0 remaining. No declaration is left with sorry.

## No longer needed

Removed the public import of
Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations, which is a withdrawn
empty module. The actual operation definitions are now imported from their adopted
upstream location. No mathematical dependency, DAG node, or module is pruned; both
first- and second-factor comparison nodes remain necessary.

LeanFinder returned general sheaf pullback comparison results rather than this
Ext cup identity. Loogle found Ext.mapExactFunctor_comp, already used by the
existing proof. The msearch grep query returned no hits; direct source searches
found the two existing factor identities and the archived consumer. No replacement
proof or additional lemma is needed for this import repair.

## Where the brief, the DAG or earlier work was wrong

The assigned module was absent from lean/ because it was quarantined, rather than
withdrawn. The rework archive contains a complete proof and zero sorries. Its
public import was not updated after the scalar operations module was retired in
favor of the upstream twin. Merely importing Field would leave the public scalar
operations unavailable, so the repair follows the canonical operations module.

The DAG already names the current upstream definitions and first-factor module;
its statement, proof, Lean attachment, and dependencies remain accurate. The two
archived consumers have independent stale public imports and remain quarantined;
this delivery does not alter their statements or proofs. No new nodes or semantic
changes were introduced.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
