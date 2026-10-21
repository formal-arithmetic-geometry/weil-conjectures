## What changed

Retired `Sheaf.AlgebraicGeometry.FiniteLocalAbelianForget` in favor of the already proved
`WeilConjectures.AlgebraicGeometry.FiniteLocalAbelianForget`, as listed in
`coord/retire-items.tsv`. The old predicate `IsLisseEtaleSheafOfSets` abbreviates the upstream
`IsFiniteLocallyConstantSheafOfTypes`. The theorem has exactly the same mathematical content
and universes. A compilation probe applies the upstream theorem to the exact old signature.

Migrated the private comparison import in these six consumer modules:

- `Sheaf.AlgebraicGeometry.ConstructibleIntegralCoefficientsBackward`
- `Sheaf.AlgebraicGeometry.ConstructibleTorsionModulesAgree`
- `Sheaf.AlgebraicGeometry.FrobeniusVectorBundleKernel`
- `Sheaf.AlgebraicGeometry.LisseStratumInteriors`
- `Sheaf.DeligneLaumon.TorsionFiniteSubsystem`
- `Sheaf.Paper.LatticeNormalizationRationalExact`

Repaired the returned packet against the current source: the newer
`ProjectiveLineConstructible.lean` delegates to the adopted upstream projective-line proof
and no longer imports or uses the retired duplicate. Removed the stale sandbox copy from
the packet, preserving that entire newer proof and its imports. The six remaining consumer
diffs are import changes only (plus the previously required unused-import cleanup below).

For return C-73e81 (delivery head 73e817eac), refreshed the consumer changes against
current sheaf-dag. In `FrobeniusVectorBundleKernel`, preserved the newly migrated private
import of `WeilConjectures.AlgebraicGeometry.EtaleStratifiedFinite`; the old packet would
have restored its obsolete Sheaf counterpart. No FlatConvolutionGradedIso source is part
of this packet. Compilation and delivery are rerun against the current server baseline.

Moved the Lean attachment of `lem-weil-pbc-finite-local-abelian-forget` to the upstream
module and corrected its stale recorded signature. Kept its mathematical statement,
proof, dependency edges, and unit route. Every parent, including unfinished parents and
archived references, still cites the same node with its existing proof available upstream.
No declaration under WeilConjectures is edited.

The first dry run additionally rejected an existing proof import of the route-pivot-dropped
`Sheaf.AlgebraicGeometry.SetLocalSystemCalculus` in `TorsionFiniteSubsystem`. Removed that
unused private import: none of the consumer statement or its current proof references a
declaration from it. Its theorem signature and existing hole remain unchanged. The old
mathematical proof plan still cites the calculus node; this delivery neither implements
that plan nor withdraws its node or pretends the calculus result has been proved.

Change record: `coord/changes/F5-finite-local-abelian-forget-retire.md` lists every downstream
consumer and records the old and new signatures. All six adapted modules are unclaimed.

## Proved and sorry left

The item starts with zero holes: the current source already proves
`AlgebraicGeometry.Scheme.finite_local_abelian_forget_iff`. This delivery is duplicate
retirement, not a new proof or decomposition: 0 of 0 holes closed, 0 holes added, 0 split off.
The replacement is the existing upstream theorem of the same name. Its `#print axioms`
reports only `propext`, `Classical.choice`, and `Quot.sound`. All six adapted consumers
compile through lcompile.py; the exact-old-signature compatibility probe also compiles.

The only existing hole in the adapted modules is unchanged:
`AlgebraicGeometry.Scheme.torsion_local_system_finite_subsystem` in
`Sheaf.DeligneLaumon.TorsionFiniteSubsystem`
(node `lem-per-torsion-finite-subsystem`). No other delivered consumer has a hole.

## No longer needed

Pruned the duplicate module `Sheaf.AlgebraicGeometry.FiniteLocalAbelianForget` and all
six remaining imports of it. Its duplicate private helper `finite_constant_value` and private
instances are removed with it; the upstream module retains its own complete proofs.
Also removed the unused direct import of `Sheaf.AlgebraicGeometry.SetLocalSystemCalculus`
from `TorsionFiniteSubsystem`, as required by the route-pivot gate. This is import cleanup
only; no mathematical dependency is claimed as resolved. No mathematical node or proof
dependency is pruned: in particular the finite-operation
refinement remains necessary to the upstream proof, and the unit route is preserved.
The retired copy's imports of EtaleSheaves, FiniteConstantAbelianRefinement,
ConstructibleSheaf.Pullback, Point.ConstantSheaf, and FiniteStalksComparison remain in
use by the upstream copy, so these modules are not claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an outstanding proof, but the synchronized item has
zero holes and is explicitly listed for retirement. Its DAG Lean record still named the
obsolete `IsFiniteLocallyConstantEtaleSheafOfSets`; the actual former signature uses
`IsLisseEtaleSheafOfSets`, an abbreviation of the upstream predicate. This is a correction
of the attachment to existing code, with no change to the node's mathematical statement.

Searches were executed through msearch.py: leanfinder on the finite local constancy
comparison returned general constant-sheaf facts; loogle found
`CategoryTheory.Sheaf.isConstant_iff_forget`; grep on the comparison name returned no
Mathlib hits. Direct searches of both library roots found the exact upstream theorem.
The existing theorem is the shortest route and makes a second formal proof unnecessary.

Preflight exposed the existing route-pivot import in the torsion consumer. It was already
present in the baseline and is unnecessary for its current declaration, whose proof is
still `sorry`; the import cleanup does not add, move, or close that hole. No upstream twin
of SetLocalSystemCalculus exists, so it is not replaced by an invented equivalent.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
