## What changed

Restored `Sheaf.AlgebraicGeometry.AffineModelCoherentObjectComparisons` from its
quarantined assignment as a public re-export of the adopted
`WeilConjectures.AlgebraicGeometry.AffineModelCoherentObjectComparisons`.
This repairs the mixed derived-pullback import failure and eliminates duplicate
ownership of the same eighteen declarations. Their signatures and definition
bodies agree with the archive; only comments, imports and one local proof
irreducibility attribute differ in the source implementation.

Updated the node's Lean attachment to the source implementation. Its mathematical
statement, proof, proof dependencies, declaration list and unit route are kept.
Change record: `coord/changes/W4-affine-model-coherent-source-reexport.md`.
The quarantine archive and all source-library files are unchanged.

Validation: the restored module compiled in 1.5–1.6 seconds. An import probe
compiled the exact archived existence-theorem signature using the source theorem,
all eighteen public declarations, and both tilde-complex constructions of the
archived Tor-amplitude consumer. It also imported the bottom-model theorem and
both Hom-equation consumers alongside the restored Sheaf path. The probe compiled
in 9.2 seconds. Axiom checks on all eighteen declarations and those three consumer
theorems show only `propext`, `Classical.choice`, and `Quot.sound`.

## Proved and sorry left

Zero-hole assigned repair: the archive contains **0** `sorry`s; the restored module
contains **0**. Holes closed: none. Holes added: none. Split-off statements: none.

`AlgebraicGeometry.exists_affineModelCoherentObjectComparisons`, node
`lem-pc-affine-model-coherent-object-comparisons`, is supplied by the existing
complete source proof, with only the allowed axioms. The same holds for all other
seventeen public declarations. No theorem with `sorry` is retained or introduced
by this delivery. This is an import/definition-ownership repair, not a claimed
new proof-hole closure.

## No longer needed

The duplicate local implementations are replaced by the existing source
implementation. Their old direct imports are subsumed by the single public source
import: `Sheaf.AlgebraicGeometry.PerfectHomTransport`,
`WeilConjectures.Algebra.Homology.ScalarExtensionHom`,
`Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`,
`Mathlib.Algebra.Homology.Additive`, `Mathlib.AlgebraicGeometry.Modules.Tilde`,
`Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric`,
`Mathlib.Algebra.Homology.BifunctorShift`, `Mathlib.CategoryTheory.InducedCategory`,
`WeilConjectures.Algebra.Homology.KFlatModuleBaseChange`,
`WeilConjectures.AlgebraicGeometry.AffineCoordinateComparisonCoherence`, and
`Sheaf.AlgebraicGeometry.PerfectHomComparisonTriangle`.

No mathematical dependency node or source-library module is pruned. In particular
the source proof still uses `AffineCoordinateComparisonCoherence`; it and its chain
have complete proofs on this base, and must remain. The old Sheaf import path is
restored, not withdrawn. No `deleted.txt` is used.

## Where the brief, the DAG or earlier work was wrong

The route note describes the older unfinished comparison chain. The current
adopted source now contains the same complete object-comparison construction;
its declaration bodies match the archive after comment/import/local-attribute
normalization. `#print axioms` establishes that the full comparison chain and the
three checked downstream results no longer rest on `sorry`.

Following the shortest-route instruction therefore means reusing that source
implementation, rather than rebuilding a specialized comparison or handing the
obligation to another statement. The zero-sorry archive was quarantined for an
import collision, not for a missing proof. The stale Lean attachment is reconciled
without weakening any statement or removing its dependencies. The unit record has
no realized statement or step for this auxiliary node, and its route is preserved.

The two archived consumers have their own rework entries. Their full restoration
is outside this item; the exact uses of this item's tilde functor were compiled
against the restored interface. There are no forced consumer adaptations.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
