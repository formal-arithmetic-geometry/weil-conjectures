## What changed

Retired Sheaf.AlgebraicGeometry.Modules.ExteriorSheafStalkComparison in favor of
WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafStalkComparison, as required
by retirement row 278. The sole direct consumer ExteriorTensorStalkKernelSpan now
imports the upstream twin. A proved private retainedExteriorSheaf_stalk_comparison
identifies the two exterior presheaves by identity section maps, sheafifies the
isomorphism, proves its wedge formula by unit naturality, and transports the
upstream stalk theorem along its linear stalk equivalence. The two existing
private calls use this bridge. All public consumer signatures and definitions
remain verbatim. No upstream or target file changes.

The comparison node's Lean attachment points to the upstream module with the
upstream signature verbatim. Its proof description and the parent's first step
record the implemented route. The change record is
coord/changes/C3-retire-exterior-sheaf-stalk-comparison.md.

## Proved and sorry left

The assigned module starts with zero sorries: 0 holes closed, 0 holes added,
0 split off, and 0 left. The upstream exteriorSheaf_stalk_comparison and the
consumer exteriorTensor_stalk_kernel_le_relationSpan remain fully proved.
The new private retainedExteriorSheaf_stalk_comparison is fully proved.
This is an API retirement, not a hole closure or decomposition.

Validation: the adapted consumer compiles cleanly through lcompile.py --all in
10.8 seconds. Separate #print axioms checks for the upstream comparison and
exteriorTensor_stalk_kernel_le_relationSpan show only propext, Classical.choice,
and Quot.sound. A source import-closure scan finds zero Sheaf/WeilConjectures
twin pairs and no reference to the retired module. All three existing public
signatures were compared with the source and are identical; all lines fit
100 columns. The
identity-on-sections bridge uses the existing uniqueness theorem for exterior
restrictions and the upstream proved theorem, rather than repeating its proof.
Searches with msearch.py (LeanFinder, Loogle, grep) and direct library inspection
confirmed that upstream is the existing comparison; the generic sheafification
and stalk functors supply the required transport.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.Modules.ExteriorSheafStalkComparison.
The consumer replaces that import with its WeilConjectures twin. It also drops
the unused proof import WeilConjectures.Topology.PresheafModuleStalkFunctor.
No mathematical node or dependency is pruned: the existing comparison node is
reattached to the proved upstream theorem, and the parent continues using it.
All thirteen downstream modules keep the same public consumer interface.

## Where the brief, the DAG or earlier work was wrong

The general proving brief describes a holed obligation, but the current queue
marks this item as retire, and the current source already contains no sorry.
The upstream theorem is not directly interchangeable at the call sites:
exteriorPower and exteriorSheaf are built from differently constructed restriction
maps. Equality on pure wedges and sheafification unit naturality supply the
required comparison, with no weakening and no new assumption.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
