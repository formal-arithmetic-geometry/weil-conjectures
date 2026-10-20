## What changed

Restored lean/Sheaf/AlgebraicGeometry/ScalarCupPullbackNaturality.lean from the
quarantine path recorded in coord/rework.tsv. Replaced its stale public import of
Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations with the canonical
WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations. The
archived theorem signature, complete proof, docstring, and proof-only imports are
unchanged. No adopted source file was modified.

The unmodified archive failed with `Unknown identifier Field` at line 54, since
Field and the scalar operations were imported only privately. With the canonical
public import the restored module compiled without errors or warnings through
lcompile.py in 15.8 seconds.

Read all four stated dependency nodes and their current Lean declarations. The
proof still applies scalarCohomologyExtEquiv injectivity and coefficient
naturality, transports Yoneda composition, uses scalarPullbackCoefficient_tensor,
and postcomposes scalarExtCup_inverseImage by the target tensor coefficient.
All three proof imports are used. The DAG statement, Lean attachment, proof,
proof_deps, and unit route already describe this exact argument and need no edits.

Change record: coord/changes/scalar-cup-pullback-naturality-upstream-import-B5.md.

## Proved and sorry left

AlgebraicGeometry.Scheme.Modules.scalarCup_pullback_naturality
(node lem-sc-scalar-cup-pullback-naturality) retains its complete proof.
This is a zero-hole quarantine repair: 0 original sorries, 0 holes closed,
0 holes added, 0 split off, and 0 remaining in the delivered module.
No new theorem or dependency obligation is introduced.

## No longer needed

Removed the public import of the withdrawn empty module
Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations and replaced it
with the existing upstream definitions. No mathematical node or dependency module
is pruned. All declared proof dependencies remain necessary.

LeanFinder returned generic sheaf pullback comparisons, rather than this scalar
cup identity. Loogle found Ext.mapExactFunctor_comp, already used in the archived
proof. The msearch grep query returned no hits. Direct source searches found the
Cech module cup naturality theorem, whose coefficient framework differs, and the
archived direct consumer. No shorter replacement or new lemma is needed.

## Where the brief, the DAG or earlier work was wrong

The module is absent because of quarantine, not mathematical withdrawal. Its
archive already contains zero sorries. The public import had not followed the
retirement of the duplicate scalar operations module. The current operation node
already names the canonical upstream definitions; restoring this import repairs
the actual failure without changing the theorem or its proof route.

The sole archived direct consumer ScalarCupPullbackCoefficientNaturality has an
independent stale public import of the same retired operations module. Its call
to scalarCup_pullback_naturality has the same signature. A validation-only sandbox copy reproduced its own line-51 `Unknown identifier
Field` error against the restored item. After replacing only its stale public
import by the canonical operations module, its unchanged theorem and proof
compiled without warnings in 6.2 seconds against the restored item. That
validation-only consumer copy is outside lean/ and is not delivered. No consumer
change is forced by this restoration; its own quarantine repair remains separate.
No statement or definition changes, new nodes, or unit-route changes are needed.

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
