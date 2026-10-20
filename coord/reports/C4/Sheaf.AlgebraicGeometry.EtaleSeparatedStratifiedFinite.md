## What changed

Retired Sheaf.AlgebraicGeometry.EtaleSeparatedStratifiedFinite, the explicit duplicate
retirement item in coord/retire-items.tsv. Its upstream twin already supplies
AlgebraicGeometry.Scheme.exists_etale_separated_stratified_finite with a byte-identical
signature and complete proof. The sole direct consumer,
Sheaf.AlgebraicGeometry.EtaleStratifiedFinite, now imports that upstream module privately.
No other line of the consumer changes. The existing node's Lean attachment moves to the
upstream theorem; its statement, proof, proof_deps and unit route stay unchanged.

Change record: coord/changes/C4-retire-etale-separated-stratified-finite.md.
No source-library file is modified. There are no forced adaptations of held modules.

LeanFinder, Loogle and grep searches were run through msearch.py; local searches of both
Lean roots found the exact source theorem. The upstream theorem was checked by a scratch
#print axioms probe: only propext, Classical.choice and Quot.sound. The redirected consumer
compiled separately through lcompile.py in 1.4 seconds without errors or warnings.
The required deliver3.py --no-push run printed OK: the packet compiles and passes
server preflight, review class CODEX. The source proof's use of the constructible
finite stratification and etale base-change
instance agrees with the node and the local Stacks 07RZ and 02GO source texts.

## Proved and sorry left

Original direct holes: zero. Holes closed: zero. Holes added: zero. Split off: zero.
No sorry remains in any delivered module. The complete theorem
AlgebraicGeometry.Scheme.exists_etale_separated_stratified_finite is reused from the
adopted source library, with only the three permitted axioms. This is duplicate retirement,
not a new proof or a decomposition. The adapted consumer already had a complete proof
and remains complete.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.EtaleSeparatedStratifiedFinite.
Removed its private import from Sheaf.AlgebraicGeometry.EtaleStratifiedFinite and replaced
it by WeilConjectures.AlgebraicGeometry.EtaleSeparatedStratifiedFinite.

The retired duplicate's public imports (LocallyClosedStratification, Etale, Finite,
Separated, Constructible) and private proof imports (ConstructibleStratifiedFinite,
QuasiFiniteLocallyQuasiFinite, UnramifiedQuasiFinite) remain in its unchanged upstream twin.
None of those mathematical dependencies or their nodes is claimed as pruned. No parent
proof dependency is removed: the three actual DAG parents still use the same theorem
node through its corrected Lean attachment. No unit statement or proof step is bypassed.
The repository and quarantine scan finds no further direct importer.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an item with sorry or an assigned repair; the current
item has zero sorry and is explicitly listed for duplicate retirement. The source theorem
and proof already agree exactly, so proving another theorem or leaving a no-op would not
perform the repair. The old node attachment named the duplicate Sheaf module; it now names
the upstream module. The retirement inventory also lists the former Sheaf affine-cover
consumer, which has already been retired; its current upstream module already imports the
upstream separated theorem and needs no edit. No mathematical statement is disputed.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
