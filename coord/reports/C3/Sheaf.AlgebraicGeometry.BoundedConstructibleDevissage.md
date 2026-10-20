## What changed

Restored lean/Sheaf/AlgebraicGeometry/BoundedConstructibleDevissage.lean from the
exact quarantine path in coord/rework.tsv. Replaced its private `import all` of
WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory by a normal
proof import of Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback.
Both proofs use the latter module's proved public `_root_.constructible_of_iso`
with `(R := R)`. All public imports and both declaration signatures are preserved.
The node records this existing helper dependency and the actual finite-truncation
argument. The complete module compiled on the server without warnings.

Change record: coord/changes/c3-bounded-constructible-devissage-transport.md.
The archived tensor-preservation consumer keeps both applications of the
unchanged devissage theorem; no consumer adaptation is necessary.

## Proved and sorry left

Assigned repair completed for both declarations:
- AlgebraicGeometry.ProEtale.isClosedUnderIsomorphisms_boundedConstructibleModule.
- AlgebraicGeometry.ProEtale.prop_of_boundedConstructibleModule.

Both belong to lem-sfb-dc-module-devissage. The archive already had zero local
holes, but failed to compile at both transport calls. Holes closed: zero.
Holes added: zero. Holes remaining in the item or added elsewhere: none.
No result is split off. The devissage proof still applies the existing fully
proved DerivedCategory.prop_of_bounded theorem.

## No longer needed

Removed the private `import all` of
WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory. Its ordinary
public import stays, since it defines boundedConstructible. No mathematical
node or module is pruned: all previous dependencies and the unit route are kept.
The old inaccessible private helper is replaced by an existing public theorem;
no duplicate helper or new mathematical obligation is introduced.

## Where the brief, the DAG or earlier work was wrong

The missing live source was quarantine, not withdrawal. The 2026-10-20 upstream
sync made the former constructibility helper inaccessible: it is private in
Sheaf.UpstreamExtra.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory.
The existing public transport theorem is at the root namespace and takes an
implicit ring, unlike the former helper. A direct proof import and explicit
root-qualified calls repair both errors without changing mathematics.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
