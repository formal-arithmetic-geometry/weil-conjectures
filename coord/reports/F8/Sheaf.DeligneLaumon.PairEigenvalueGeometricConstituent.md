## What changed

Replaced the hole in `AlgebraicGeometry.WeilSheaf.exists_pair_eigenvalue_geometric_constituent` by a complete proof from a structural geometric-orbit lemma. The original theorem signature is unchanged.

The proved private helper `eigenvalue_summand` takes a nonzero eigenvector through a direct-sum isomorphism and selects a nonzero projection using the biproduct identity. It proves Frobenius compatibility of that projection. The proved private helper `subobject_of_cokernel` constructs the inverse-image subobject by an actual categorical pullback, proves its kernel and cokernel properties, obtains the cokernel isomorphism, and proves lissity using the kernel of a difference map. The main proof powers the eigenvalues, selects two summands, uses the orbit transport to align them, and embeds the resulting quotient diagram into the exact restriction of the ambient sheaf.

Added `Sheaf.DeligneLaumon.GeometricConstituentOrbit`, a statement about a simple sheaf alone: finite geometric direct-sum decomposition, exact restriction and point transports. It contains no selected eigenvalues and no ambient subquotient diagram. This isolates the geometric/constant-extension steps rather than restating the original eigenvalue/subquotient conclusion. Its docstring and node give the full geometric-socle, multiplicity and point-transport argument, including the zero-dimensional case.

Replaced the item's unused public import of `WeilConjectures.DeligneLaumon.Reduction.RealCurve` by the smaller smoothness, geometric-connectedness and lisse-filtration interfaces. Added private proof imports for the orbit theorem, geometric irreducibility under isomorphism and stalk isomorphisms. The only direct Lean importer, `PairEigenvalueCurveTest`, already publicly imports `RealCurve`, so it retains the same available interface. The change record is `coord/changes/F8-pair-eigenvalue-geometric-imports.md`.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.WeilSheaf.exists_pair_eigenvalue_geometric_constituent`, node `lem-zl-pair-eigenvalue-geometric-constituent`. Its module now contains zero `sorry`s.

Added one remaining hole: `AlgebraicGeometry.WeilSheaf.exists_geometric_constituent_orbit`, node `lem-zl-geometric-constituent-orbit`, in the new module `Sheaf.DeligneLaumon.GeometricConstituentOrbit`.

This is a decomposition: one hole closed and one hole added, net zero. It proves the eigenvalue-projection and ambient-subquotient portions of the argument; the geometric orbit and constant-extension construction remain. Both helper proofs are complete, with no additional assumptions or holes.

Validation: final compilation passed without warnings: 4.4 s for the structural lemma and 24.7 s for the item. The unchanged direct consumer `PairEigenvalueCurveTest` also compiled against the reduced public interface (89.9 s; this unchanged file is not included in the delivery). No profiling options remain.

## No longer needed

Removed the direct public import `WeilConjectures.DeligneLaumon.Reduction.RealCurve`. No weight, purity or curve theorem is used by this argument. `WeilConjectures.WeilSheaf.GeometricConstituent` was considered during development but is unnecessary; the proof uses only the smaller `IrreducibleLisse` API and `StalkIso`.

The item's proof dependencies are now just `lem-zl-geometric-constituent-orbit`; its proved categorical and eigenvector steps use no unfinished dependency. The former direct dependencies `lem-zl-affine-geometric-components-finite-extension`, `lem-zl-geometric-constituents-any-base`, `lem-zl-constant-extension-weil-heart-equivalence`, `def-weil-local-frobenius-trace`, and `lem-zl-point-weil-heart-flag` belong to the remaining structural argument and remain recorded on its node.

The former dependencies `lem-zl-classical-weil-filtration-heart-transport` (`Sheaf.Paper.ClassicalWeilFiltrationHeartTransport`) and `lem-zl-curve-restriction-filtration-spectrum` (`Sheaf.Paper.CurveRestrictionFiltrationSpectrum`) are unnecessary for the inverse-image construction and eigenvalue projection. These steps are now proved directly in the actual source category. This is pruning of this argument only: the unit's own nodes and route are retained, and no global module withdrawal is claimed. No source-tree declaration is removed or changed.

## Where the brief, the DAG or earlier work was wrong

Several declared dependencies are phrased in the common-stage Weil heart, whereas this item is in the source pro-etale category. In particular, the common-stage filtration transport and curve spectrum statement do not provide the actual categorical pullback diagram used here. The source lisse-kernel and cokernel APIs do provide it, and the delivery proves that step from them.

The existing representation Clifford theorem states a filtration, not a geometric direct-sum orbit with point transports. Likewise the common-stage constant-extension equivalence is not by itself the source-category construction. The new remaining node explicitly includes that source realization and its local comparison as proof obligations. No identification of the two categories is assumed by the completed proof.

Checked the new statement against the zero object, an empty base, zero summands, coincident x and y, and a zero-dimensional support. Nonzero stalk assumptions exclude the first three degeneracies; the construction allows the same point twice and uses an affine line for zero-dimensional support. The orbit transport preserves both the original image and the residue cardinality, so the exponents used for beta do not change.

Searches used LeanFinder, Loogle, LeanSearch and Mathlib grep, plus searches of both project roots. Blueprint searches for geometric constituents and Frobenius orbits found the existing filtration node, but no decomposition with the point transports required here.

## New nodes

`lem-zl-geometric-constituent-orbit` records the geometric-socle/Frobenius-orbit and source constant-extension portion of the original proof. It is independent of eigenvalue choices and ambient diagrams; the completed proof combines it with actual eigenvector projection and pullback constructions. The node records three kinds of Mathlib search, its current blueprint source, a complete proof in words and its verbatim Lean statement. No existing definition or statement signature changes.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
