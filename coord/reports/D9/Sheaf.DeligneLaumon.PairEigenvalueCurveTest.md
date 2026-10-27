## What changed

Replaced the proof hole in
`AlgebraicGeometry.WeilSheaf.exists_pair_eigenvalue_curve_test` with a complete
Lean assembly. Its statement, existing docstring and public import are unchanged.
Added private proof imports for two new obligations, the existing source
pro-etale irreducibility detector, finite-cover Bertini and the proved
irreducible-local-system isomorphism API.

The proved private helper `exists_geometric_curve_pair` actually constructs the
geometric curve. In dimension at least two it uses the detector for a singleton
family and finite-cover Bertini through the two canonical geometric lifts; the
connected detector pullback proves irreducibility of the restricted quotient.
In dimension one it uses the geometric base and its identity immersion. The
point set may be a singleton. This reproduces the existing curve-testing argument
without importing RealSheaves, which would cause a cycle.

The public proof first aligns the eigenvalues in a geometric simple quotient on
a positive-dimensional base, applies that proved helper, and descends the given
curve and diagram. It transfers powered eigenvalues using
`Module.End.HasEigenvalue.pow` and equality of characteristic polynomials,
multiplies the two pairs of exponents, composes the reality implications, gives
the final field the composed algebra map, and verifies the composite structure
square using `Spec.map_comp`. The local residue cardinalities and point images
are composed explicitly. No definitions or data chosen inside definitions were
added, and no source-library file was edited.

The remaining obligations are separate geometric-constituent alignment before
any curve is selected, and descent of an already given geometric curve with its
restricted quotient already known irreducible. Neither is the original theorem
under another name: the first has no dimension-one conclusion or Bertini step;
the second has no eigenvalue alignment, no simple arithmetic input quotient,
and no curve-existence step. Their composition requires the geometric curve
construction and the polynomial, field and exponent calculations now proved in
the assigned module. This is a decomposition, not a completed proof of both
geometric and descent inputs.

Validation: both new modules compiled through lcompile. The parent elaborated
successfully after replacing an expensive geometric-point definitional
comparison by its explicit pullback projection proof. A profiler run then
finished in 25.9 seconds; development profiler options were removed. The
existing theorem signature and docstring match the original verbatim, each
Lean line is at most 100 characters, and the node Lean statements match their
new declarations. The final clean parent compile passed without warnings in 46.8 seconds.
The final dimension-one branch uses explicit smoothness and irreducibility
witnesses, reducing elaboration through the identity pullback.

## Proved and sorry left

Original item: 1 hole. Item after the delivery: 0 holes.

Closed by decomposition:
`AlgebraicGeometry.WeilSheaf.exists_pair_eigenvalue_curve_test`
(node `lem-zl-pair-eigenvalue-curve-test`).

Added and remaining: 2 holes, each the whole proof of a named public theorem in
its own new module:

- `AlgebraicGeometry.WeilSheaf.exists_pair_eigenvalue_geometric_constituent`
  (`Sheaf.DeligneLaumon.PairEigenvalueGeometricConstituent`, node
  `lem-zl-pair-eigenvalue-geometric-constituent`).
- `AlgebraicGeometry.WeilSheaf.exists_geometric_curve_diagram_descent`
  (`Sheaf.DeligneLaumon.GeometricCurveDiagramDescent`, node
  `lem-zl-geometric-curve-diagram-descent`).

The three private helpers are proved and have no holes. The delivery adds no
other holes. The net textual hole reduction for this packet is -1; the genuine
completed work is the geometric curve construction and the combination of
constant-field and curve-local comparisons.

## No longer needed

No existing import removed, no module withdrawn, and no global pruning claimed.

The item now directly depends on the two new nodes and the existing
`lem-zl-proetale-irreducibility-detector` and
`lem-zl-bertini-finite-cover-curve`.

The previous direct dependencies
`lem-zl-affine-geometric-components-finite-extension`,
`lem-zl-geometric-constituents-any-base`,
`lem-zl-constant-extension-weil-heart-equivalence`,
`lem-zl-geometric-closed-curve-smooth-model`,
`lem-zl-classical-weil-filtration-heart-transport`,
`lem-zl-curve-restriction-filtration-spectrum`, and
`lem-zl-point-weil-heart-flag`
are now dependencies of the relevant two remaining obligations. None is claimed
to be globally unnecessary. No unused proof-dependency import was added, and no
upstream declaration was removed or reverted to sorry.

## Where the brief, the DAG or earlier work was wrong

The planned geometric-constituents theorem
`Representation.exists_filtration_isIrreducible_restrict` gives a filtration of
a representation; its signature supplies neither the source Weil-category
transport nor simultaneous selection of two local eigenvalues on one geometric
simple quotient. The existing sheaf Clifford results give geometric subsheaves
and semisimplicity on an irreducible geometric base, but do not expose this
simultaneous local selection interface. The first new node states that missing
part before curve construction, including the supporting component and the
zero-dimensional affine-line replacement.

Likewise the constant-extension heart equivalence, classical-filtration
transport, curve-spectrum and point-flag declarations use the raw/common-stage
category. They do not directly accept the source `AlgebraicGeometry.WeilSheaf`
used by this item. Source pro-etale iterated Weil transport is constructed in
`WeilConjectures.WeilSheaf.BaseChangeField.Transport`; local pullback power
comparisons also exist in the source tree. Their combination with a descended
curve and its actual subquotient diagram remains the second obligation. No
unproved category identification was inserted into the parent proof.

Edge cases checked: empty X and zero quotient cannot have the assumed local
eigenvalues; two points may coincide; the two selected eigenvalues may differ
at that point; a positive-dimensional base of dimension one needs no Bertini;
a zero-dimensional supporting component is a finite-field point and its simple
quotient is one eigenline, so its affine line provides the positive-dimensional
base. Nonsplit ambient extensions and Jordan blocks are permitted. Distinct
roots may acquire equal powers; reality is a condition on the whole powered
ambient spectrum with multiplicities. Geometric irreducibility is required only
for the selected quotient, never for the ambient sheaf.

## New nodes

`lem-zl-pair-eigenvalue-geometric-constituent` realizes the supporting-component,
geometric-socle, Frobenius-orbit and eigenvalue-alignment part of paragraphs 1
and 7. Its module has one named whole-proof sorry, a source and a full proof in
words. It does not select a curve. The existing geometric-constituent,
constant-extension, point and transport dependencies are retained there.

`lem-zl-geometric-curve-diagram-descent` realizes the finite-model, exact diagram
restriction and local polynomial-power part of paragraphs 2--3. It assumes the
geometric curve, its two lifted points and irreducibility after geometric
restriction. Its module has one named whole-proof sorry, a source and a full
proof in words. LeanSearch, LeanFinder and Mathlib grep queries for both new
nodes were run through msearch and logged; no matching theorem was found.
Whole-blueprint and local-library searches found the existing constituent and
curve-testing inputs, not these source-category interfaces. An overlay traversal
verified that neither new node reaches the parent. The unit route is retained.

No existing signature or definition changed, so no change record or consumer
adaptation is required.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
