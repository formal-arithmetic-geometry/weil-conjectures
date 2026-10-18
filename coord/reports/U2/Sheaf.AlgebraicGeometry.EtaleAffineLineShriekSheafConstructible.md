## What changed

Proved `AlgebraicGeometry.isConstructibleEtaleModuleSheaf_affineLine_shriek` with its original signature. The proof implements finite-type integer descent of the input, compact-support and homology base change, and well-founded induction on closed subsets. The compact-support comparison uses the existing source-library exchange isomorphism and compactification-independence API.

Added three proved modules, each with its own node: `AffineLineDenseOpenFiniteComplement`, `EtaleAffineLineLisseFiniteComplement`, and `EtaleAffineLineShriekFiniteTypeDenseOpen`. The first constructs dense affine shrinking and a finite boundary using generic fibres, dimension one, generic finiteness and finite prime avoidance. The second combines this construction with generic constancy. The third applies the stated lisse and quasi-finite shriek results and the open-closed triangle; constructible homology being triangulated supplies the Serre argument.

The repair removes the duplicate private `compactSupport_homology_baseChange_iso` declaration from `EtaleAffineLineShriekFiniteTypeDenseOpen`. Its proof site now composes the existing lower-shriek base-change map, homology map, single-functor map, and compactification-independence isomorphism directly.

The main theorem's DAG proof now records this implementation. No existing statement, definition, target signature, or public import was changed. All helper definitions are explicit constructions inside proofs. Choices of compactifications occur only in theorem proofs.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.isConstructibleEtaleModuleSheaf_affineLine_shriek`.

Also proved the three new public declarations:

- `AlgebraicGeometry.AffineSpace.exists_dense_affine_open_isFinite_closedComplement`.
- `AlgebraicGeometry.exists_dense_affine_open_lisse_finite_complement`.
- `AlgebraicGeometry.exists_dense_open_affineLine_shriek_constructible`.

No `sorry` remains in any delivered module. Holes closed: 1 original. Holes added: 0. The repair removes one duplicate helper declaration and leaves the existing named dependencies unchanged. In particular, the existing lisse-open-relative-line, quasi-finite shriek, generic-finiteness-neighborhood, open-closed compact-support triangle, and compactification-category declarations remain dependencies, with their existing proof status unchanged.

Validation: all delivered files are checked through `lcompile.py` and the required `deliver3.py --no-push` gate. The proofs cover empty schemes, zero coefficient rings, zero sheaves, arbitrary integer degrees, reducible bases, and nonreduced bases. The finite closed complement is constructed by an actual pullback; the proof does not assume equality of independently chosen reduced closed structures.

## No longer needed

Removed these private imports from the original item (and removed the temporary direct import of
`WeilConjectures.CategoryTheory.DerivedCategory.Constructible`, needed only in the dense-open module):

- `Sheaf.AlgebraicGeometry.EtaleCompactSupportBaseChangeQcqs`: the existing proved source-library compact-support exchange map is used directly. The duplicate node `lem-weil-pbc-etale-compact-support-base-change-qcqs` is no longer a direct dependency of this proof.
- `Sheaf.RingTheory.FiniteRingMapQuasiFinite`: Mathlib's `IsFinite` to `LocallyQuasiFinite` instance and `quasiFiniteAt_iff_isOpen_singleton_asFiber` provide the precise quasi-finiteness predicate. The node `lem-weil-pbc-finite-ring-map-quasi-finite` is not used here; its obsolete top-level tool-use entry was removed.
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`: use the source-library exact inverse-image API, already imported explicitly.
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`: the explicit comparison module supplies the needed equivalence.
- `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`: needed only by the local finite-boundary argument through `QuasiFiniteShriekConstructible`.
- `WeilConjectures.ConstructibleSheaf.KernelCokernel`: closure is used through the existing triangulated constructible-homology API.
- `WeilConjectures.ConstructibleSheaf.GenericConstancy`: used in the new lisse-boundary module.
- `Sheaf.AlgebraicGeometry.EtaleCompactSupportOpenClosedTriangle`: used in the new dense-open module.
- `Sheaf.AlgebraicGeometry.LisseOpenRelativeLineConstructibility`: used in the new dense-open module.
- `Sheaf.AlgebraicGeometry.Morphisms.GenericFiniteOpenNeighborhood`: used in the new geometric shrinking module.
- `Sheaf.AlgebraicGeometry.QuasiFiniteShriekConstructible`: used in the new dense-open module.

The last eight removals reorganize direct imports; their needed declarations remain below the new nodes. No global pruning of modules reached by other parents is claimed. The unit's own realized statements and proof steps are preserved. No finite affine-cover gluing lemma is needed: finite prime avoidance supplies one dense principal affine open.

The removed private helper `compactSupport_homology_baseChange_iso` is no longer needed in the finite-type module; its composition is written at the sole call site from the existing imported API.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was found. The existing plan leaves substantial glue implicit: connected-limit preservation for affine space, Noetherian induction with arbitrary closed scheme structures, and the cohomology-level base-change comparison. These are now proved explicitly.

The earlier delivery duplicated the cohomology-level base-change statement as a private theorem in the finite-type module even though the item module already stated the same fact. The duplicate is removed; the finite-type proof uses the lower-shriek API directly.

The generic-fibre proof can avoid a separate theorem identifying generic points of relative affine-line components. The projection is an open continuous surjection, so the image of a dense open is dense open and contains every component generic point. Its generic fibre therefore has a nonempty open; the existing dimension-one finite-boundary theorem applies. The source-library triangulated constructible-homology API also avoids manually constructing the five-term kernel/cokernel extension.

## New nodes

`lem-weil-pbc-affine-line-dense-open-finite-complement` records the proved geometric shrinking theorem, including the empty and nonreduced cases, in `lean/Sheaf/AlgebraicGeometry/AffineLineDenseOpenFiniteComplement.lean`.

`lem-weil-pbc-affine-line-lisse-finite-complement` records the proved combination of generic constancy and geometric shrinking in `lean/Sheaf/AlgebraicGeometry/EtaleAffineLineLisseFiniteComplement.lean`.

`lem-weil-pbc-affine-line-shriek-finite-type-dense-open` records the proved localization step in `lean/Sheaf/AlgebraicGeometry/EtaleAffineLineShriekFiniteTypeDenseOpen.lean`.

All three carry source references, complete proof descriptions, search records, and Lean signatures. No change record is required because no existing interface or definition changed.

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
