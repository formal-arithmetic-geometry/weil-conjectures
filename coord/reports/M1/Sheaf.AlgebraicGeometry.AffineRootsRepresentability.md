## What changed

Proved `AlgebraicGeometry.affineRoots_representability` in full, without changing its
statement or the definitions `affineRootsOver` and `affineRootsCoordinate`.
Four proved private helpers establish the quotient relation, uniqueness and existence
of over-morphisms with a specified coordinate, and the sectionwise kernel equivalence.
The proof uses `AdjoinRoot.lift`, `AdjoinRoot.ringHom_ext`, `ΓSpec.adjunction`,
`PreservesKernel.iso`, `AddCommGrpCat.kernelIsoKer`, and `Over.mapPullbackAdj`.
Naturality and both base-change formulas follow from composition on global sections
and the pullback projection equation. No new public declaration or module is added.

Read Stacks Tags 040M and 03PK in the local groupoids and etale-cohomology sources.
Searches via leanfinder, loogle and grep found the quotient API and no replacement
for the entire theorem. The proof works for the zero ring, empty test schemes,
nonreduced rings and characteristics dividing n: it uses only commutative-ring
identities, kernel preservation and pullbacks. Positivity is used exactly to construct
the coordinate's inverse as its (n-1)st power; n=1 is included.

Updated the node's sheaf-identification proof step and dependencies to match the Lean.
Removed one unused public import, recorded in
`coord/changes/M1-affine-roots-representability-import.md`.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.affineRoots_representability`
(node `lem-asd-affine-roots-representability`).
No holes remain in the item; no holes are added or split off.
All four private helpers are proved. Final single-file compilation passes in 6.8 seconds,
with no warnings. `#print axioms` reports exactly `propext`, `Classical.choice`,
and `Quot.sound`; its temporary command was removed before delivery.
`tools/downstream.py` reports zero downstream modules.

## No longer needed

Removed the public import
`WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf`.
The proof no longer needs node `lem-weil-pbc-small-etale-representable-presheaf-sheaf`:
the natural isomorphism with the kernel sheaf already identifies the representable
presheaf as a sheaf. Removed this node from proof_deps, the corresponding step's uses,
and the inherited tool_uses approval. Its statement dependency remains because the
unchanged node statement explicitly cites it. No module is withdrawn or deleted;
other consumers may still need that general sheaf theorem. Every other declared
proof dependency is used. The unit's realized route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The DAG's separate representable-sheaf
application is redundant for the displayed presheaf isomorphism: the roots sheaf
already supplies the sheaf condition. No consumer statement or target was changed.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
