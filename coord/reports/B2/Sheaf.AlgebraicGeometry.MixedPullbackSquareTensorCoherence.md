## What changed

Restored lean/Sheaf/AlgebraicGeometry/MixedPullbackSquareTensorCoherence.lean as a public
compatibility import of the complete adopted source module
WeilConjectures.AlgebraicGeometry.MixedPullbackSquareTensorCoherence. The archived module
failed at its obsolete local irreducibility attribute on derivedPullback, which is now
already irreducible. All declarations, docstrings and proofs from the comparison definition
onward are byte-identical in the archive and source. Reusing the source preserves the API
and avoids duplicate declarations when source and Sheaf import paths coexist.

Updated only the lean attachment of node lem-sc-mixed-pullback-square-tensor-coherence to
the adopted source module, with existing: true and both original declaration names.
Its mathematical statement, statement dependencies, proof, proof dependencies, proof
origin, source and unit route are unchanged. The quarantine archive remains intact.
No upstream source file or target is edited. Change record:
coord/changes/B2-restore-mixed-pullback-square-tensor-coherence.md.

Validation through lcompile.py: wrapper compiled in 2.6 seconds; a consumer compiled in
8.0 seconds with no warnings. The consumer proves the exact archived comparison formula
by rfl, applies the theorem at the full verbatim archived signature, and coimports the
restored Sheaf path, source path, adopted downstream tensor-pairing parent, and all three
old Sheaf dependency paths. Both public constants pass #print axioms with only propext,
Classical.choice and Quot.sound. A second consumer, importing only the restored Sheaf path, also compiles in 7.7 seconds; it repeats the definition equality, full signature and axiom checks. The import-direction checker permits the source import.

## Proved and sorry left

This assigned quarantine restoration starts with zero sorries and ends with zero sorries.
Holes closed: none. Holes added: none. Split off: none. This is an API/build repair,
not a new hole reduction. Both AlgebraicGeometry.mixedPullbackSquareComparison and
AlgebraicGeometry.mixedPullbackSquareComparison_tensor are restored through their existing
complete source implementations (node lem-sc-mixed-pullback-square-tensor-coherence).
Every imported source proof dependency is already free of sorryAx, as the two axiom scans
confirm. No hollow definition or new theorem is introduced.

## No longer needed

Removed the archived direct imports Sheaf.AlgebraicGeometry.MixedHomTensorPullbackIso,
Sheaf.AlgebraicGeometry.DerivedPullbackComposition, Mathlib.AlgebraicGeometry.Pullbacks,
and the private Sheaf.AlgebraicGeometry.DerivedPullbackCompositionTensorKFlat import.
The adopted square module publicly supplies the exact statement interfaces via
GlobalHomAdjunctionIso, DerivedPullbackComposition and Mathlib.AlgebraicGeometry.Pullbacks;
its unchanged proof privately imports the adopted DerivedPullbackCompositionTensorKFlat.
The old Sheaf composition module is already an empty retirement stub. The other Sheaf
paths are compatibility imports. No mathematical node or proof dependency is pruned:
K-flat coordinates, composition/tensor compatibility and both normalization interfaces
remain needed by the exact adopted proof. No module is withdrawn or put in deleted.txt.
The unit statement and every unit proof step remain in place.

## Where the brief, the DAG or earlier work was wrong

The item is a zero-hole rework assignment, not an unfinished proof. Its earlier complete
proof had become incompatible with the current reducibility status of derivedPullback.
The adopted source now already contains the entire proof unchanged, so repeating the
archived declarations would duplicate its public API. The node's old lean attachment
pointed to a quarantined path; it now points to the actual source declaration while the
old path is restored as a compatibility import.

Read the dependency statements and source signatures first, including the complete K-flat
composition triangle restored by F4. LeanFinder located ordinary sheaf pullback comparison
isomorphisms, Loogle located tensorHom_comp_tensorHom, and msearch grep returned no square
match. Direct repository search located the exact complete source implementation, which
is the shortest route. Read the local Stacks cohomology.tex proofs of 079U and 0D5S and
Remark 08HY; the unchanged proof follows their K-flat tensor/composition normalization.
The DAG parent remains lem-sc-mixed-tensor-pairing-base-change-identity, now adopted in
WeilConjectures.AlgebraicGeometry.MixedTensorPairingBaseChangeTransport. Zero current
Sheaf importers is not grounds for withdrawing this mathematical obligation.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
