## What changed

Proved `CategoryTheory.Abelian.LeftResolution.totalizedAugmentation_natural_quasiIso`
with its existing statement unchanged. The proof combines the source library's
`QuasiIso (Λ.totalπ' K)` instance with `Λ.totalπ'_naturality φ`.
The source already contains the complete argument planned by this node; no additional
resolution or comparison development is needed.

Kept only the public import of
`WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.CochainComplexMinus`,
which supplies the statement's definitions and the two proved results.
Updated the node's proof, proof dependencies, and proof origin to record this reuse.
No definitions, theorem signatures, consumers, or unit steps changed.

Validation: the reduced-import module compiled cleanly using `lcompile.py`.
A temporary `#print axioms` check of the proved theorem reported only
`propext`, `Classical.choice`, and `Quot.sound`; the check command was then removed.
The proof applies the existing results universally, including the zero complex,
a complex concentrated in degree zero, and maps between complexes with different bounds.

## Proved and sorry left

Closed 1 existing hole:
`CategoryTheory.Abelian.LeftResolution.totalizedAugmentation_natural_quasiIso`
(node `lem-sfb-left-resolution-totalized-augmentation`).
Zero holes remain in the delivered module. Zero holes added. Zero statements split off.
This is a proof from already proved source results, not a decomposition.

## No longer needed

Removed the public import of
`Sheaf.Algebra.Homology.LeftResolutionBicomplexTotalExists` and removed its node
`lem-sfb-left-resolution-bicomplex-total-exists` from proof dependencies.
Its unproved bundled theorem is unnecessary here: the source module already
constructs the same totals by proved instances. The existing statement dependencies
are preserved, since they describe the constructions used by the node.
This does not assert that the module is unused by other parts of the project.

Removed redundant direct public imports of
`WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.Basic` and
`WeilConjectures.FromJoel.Algebra.Homology.BicomplexRows`, and the redundant
proof import of `WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns`.
All three remain available transitively through the retained source import.
The objectwise augmentation, single-row construction, and bounded comparison nodes
remain mathematical dependencies of the existing source proofs; they are not pruned.
No new imports or nodes are needed.

## Where the brief, the DAG or earlier work was wrong

The planned argument is correct, but its two conclusions are already proved verbatim
in the source module which the assigned module already imported: naturality at
lines 172–198, and the quasi-isomorphism instance at lines 202–206.
The separate holed total-existence wrapper was an unnecessary import.
The retained source proof follows the prescribed bounded-column comparison route.
Searches used LeanFinder, Loogle, the launcher's grep, and direct repository `rg`;
Mathlib search did not find the exact specialized result, while repository `rg`
located these two source declarations. No statement or definition repair is necessary.

The dry run required a change record for removing public imports. Added
`coord/changes/left-resolution-totalized-augmentation-imports.md` with the exact
old and new import lists and the downstream-user check (zero downstream modules).
No declaration's signature or definition changes, and no consumer adaptation is needed.

## Second reading by E6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
