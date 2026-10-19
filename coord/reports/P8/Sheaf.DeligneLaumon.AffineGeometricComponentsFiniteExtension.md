## What changed

Proved `AlgebraicGeometry.exists_affine_geometric_components_finite_extension` in
`Sheaf.DeligneLaumon.AffineGeometricComponentsFiniteExtension`, preserving its signature
and every field of `AffineGeometricComponentDecomposition`.

The proof indexes the geometric components by `ConnectedComponents X`, descends their
compact opens to finitely generated subalgebras, and promotes these to finite
intermediate fields. The supremum of the finitely many fields gives a common finite
extension; finite-field uniqueness identifies it with `D.extensionSubfield e he`.
Surjectivity of scalar extension reflects the partition. The restricted open schemes
are also closed, hence affine. Cartesian restriction and pullback pasting provide the
canonical `baseComponent` maps, both projection equations, component ranges, and the
bijection. Connectedness after algebraic closure proves geometric connectedness.
Base-change stability and composition prove the smooth relative dimension assertion.
All private helper declarations are proved; there are no new public declarations.

The empty case is included: the component index is empty, the supremum is the bottom
intermediate field, and its degree is one. No nonemptiness of the original scheme or
positive smooth dimension is assumed. The unit route remains unchanged: this is a
proof of the same finite-component descent tool, not a bypass of a unit statement or
step. The unit record `sk-p-dl-general-relative-line` has no realized nodes here.

Updated only `proof`, `proof_deps`, `proof_origin`, and obsolete top-level `tool_uses`
in the existing node `lem-zl-affine-geometric-components-finite-extension` to match
this argument. No definitions, statements, or other modules were changed.

Validation: launcher single-file compilation succeeded in 5.3 seconds before removing
one redundant `change` tactic. An explicit `#print axioms` of the main theorem reported
only `propext`, `Classical.choice`, and `Quot.sound`. The diagnostic command was then
removed from the delivered source; final compilation and delivery preflight are run
on that final source.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.exists_affine_geometric_components_finite_extension`
(node `lem-zl-affine-geometric-components-finite-extension`).

Proved 1 of 1 original sorries; added 0; split off 0. No sorries remain in the delivered
module or any helper. This is a proof, not a decomposition into new unproved statements.
The main theorem's axiom check also confirms that no imported sorry is used.

## No longer needed

Removed proof imports:

- `Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra`: scheme-level Noetherian instances
  replace a coordinate-ring finite-type calculation.
- `Sheaf.AlgebraicGeometry.SpecSurjectiveBaseChange`: general scheme surjectivity
  under cartesian base change replaces the affine tensor-spectrum calculation.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: the directly available open-immersion
  instance for smooth relative dimension zero suffices.
- `Mathlib.RingTheory.Spectrum.Prime.Noetherian`: use
  `Mathlib.AlgebraicGeometry.Noetherian` on the finite-type geometric base change.
- `Sheaf.FieldTheory.UniqueSubfieldOfClosure`: its needed declaration is already
  publicly imported by the unchanged statement import `Sheaf.Paper.FiniteFieldFiber`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the proof uses
  `baseChangeMap`, cartesian restriction and pasting directly, available through the
  remaining imports; the module's extra conventions are unused.

Removed proof-dependency nodes:

- `lem-weil-pbc-fibre-product-affine-spectra`: no affine tensor presentation is needed.
- `lem-pc-affine-finite-type-algebra`: use scheme-level Noetherianity directly.
- `lem-wf-affine-noetherian-components`: likewise replaced by finite-type-over-
  Noetherian scheme instances and the already used component topology API.
- `lem-weil-pbc-spec-surjective-base-change`: use scheme-level base-change stability.
- `lem-weil-pbc-spec-clopen-idempotent`: clopen inclusions are closed immersions.
- `lem-weil-pbc-affine-open-section-vanishing-prime`: a closed immersion into an affine
  scheme has affine source; no basic-open localization description is needed.
- `lem-weil-pbc-open-immersion-etale`: use smooth relative dimension zero directly.

Withdrew the obsolete top-level tool approvals for
`lem-pc-affine-finite-type-algebra` and
`lem-weil-pbc-spec-surjective-base-change`, retaining the others in their original order.
The finite-subfield uniqueness node remains needed despite its redundant direct import.
No module files are withdrawn: these nodes may still be needed by other parents.

## Where the brief, the DAG or earlier work was wrong

No statement correction was necessary. The original plan made avoidable affine
coordinate-ring detours in Noetherianity, scalar-extension surjectivity, and affineness
of clopen components. Mathlib's scheme-level APIs close those steps directly. Its
algebraic and intermediate-field APIs also combine the finite coefficient fields
without an explicit union-of-generators construction. These changes shorten only the
internal implementation of the same descent argument.

The resumed session recovered a complete sandbox proof after the provider interruption.
There was no report or delivery result in the sandbox, and the shared ledger had no
entry for this item. Recompilation confirmed the proof; one redundant tactic was removed.

## Second reading by P8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
