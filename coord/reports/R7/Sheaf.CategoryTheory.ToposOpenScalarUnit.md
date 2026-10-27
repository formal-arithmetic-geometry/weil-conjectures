## What changed

Proved ordinary extension/scalar balancing by uniqueness of the composite left adjoints.
The scalar-restriction square is the identity on sections. Its normalized Hom equation
gives the generator formula at scalar one; linearity gives every scalar. This proof is
`ordinaryExtensionComparison`, with proved private helpers `scalarRestrictionSquare`,
`scalarRestrictionSquare_apply`, `scalarAdjunction`, and `tensorSection_smul`.

The actual derived open unit is implemented in `toposOpenDerivedUnit_isIso`: subterminality
makes each nonempty section index set a singleton, so the raw extension unit is its
unique direct-sum inclusion. Restriction/sheafification compatibility and the exact
localization unit formula finish the proof.

The ordinary restriction comparison is implemented in `exists_toposOpenScalarRestriction`
by the element projection/sheafification compatibility, with the pure-tensor formula.

The final adjunct formula is proved directly from unit coherence using the actual
adjunction Hom formula and beta followed by beta inverse.

The original theorem is assembled from the proved ordinary extension and restriction
comparisons, proved actual-unit invertibility, and the separate derived lift `exists_toposOpenScalarDerivedFromOrdinary`. The latter retains the
K-flat representative equations and the actual open-unit coherence as its conclusion;
it assumes both ordinary isomorphisms and their generator formulas, which the parent
now proves. Actual-unit invertibility is proved separately and is no longer part of
the residual theorem.

The original section definitions move verbatim to `ToposOpenScalarBasic`, publicly imported
by the original module. This avoids a dependency cycle and changes no mathematical data or
public declaration signature. See `coord/changes/r7-topos-open-scalar-section-module.md`.

## Proved and sorry left

Closed original hole: `SheafOfModules.ToposOpenScalar.exists_toposOpenScalarUnit`.
Added one hole: `SheafOfModules.ToposOpenScalar.exists_toposOpenScalarDerivedFromOrdinary`
(node `lem-pur-topos-open-scalar-derived-from-ordinary`). This is one decomposition,
not a net hole reduction and not an axiom-free proof of the whole result.
Also proved `SheafOfModules.ToposOpenScalar.toposOpenDerivedUnit_isIso` and
`SheafOfModules.ToposOpenScalar.exists_toposOpenScalarRestriction`.
No sorry occurs in any definition or private helper. `ToposOpenScalarBasic` has zero holes.

Validation: the ordinary extension proof compiled in 27.8 seconds, and the parent
assembly with its direct adjunct proof compiled in 28.7 seconds. The actual-unit
module compiled cleanly in 50.9 seconds; the final ordinary restriction comparison
compiled cleanly in 24.4 seconds. The delivery tool checks the complete packet in
dependency order. The original theorem signature and all seven moved definition
bodies were compared verbatim with the current repository.

## No longer needed

The obsolete top-level `tool_uses` approvals for the replaced presentation/generator
route were removed from the parent node; no approvals were added or reordered.

The parent proof no longer uses or imports `Sheaf.CategoryTheory.Sites.BinaryCoverSitePresentation`
(`lem-sp-binary-cover-site-presentation`) or `Sheaf.CategoryTheory.RingedSliceTensorGenerators`
(`lem-sf-ringed-slice-tensor-generators`): scalar-adjunction uniqueness proves ordinary
balancing directly on the existing element site, including its unit generator formula.

The parent's direct proof also no longer imports `KFlatResolutionIndependentCoefficients`,
`RingedOpenTotalTensorKFlat`, or `RingedOpenFlatResolution`. Their mathematics was not
withdrawn: K-flat resolution remains in the residual node's proof. The proposed residual
route uses normalized scalar adjunctions and their mates, with inverse-image K-flatness,
so it does not need extension-by-zero preservation of K-flatness or flat terms from
`lem-sf-ringed-open-total-tensor-kflat` and `lem-cbc-ringed-open-flat-resolution`.

No module is withdrawn. All existing public imports remain. No source-library declaration
is deleted or changed. The unit's route remains through the original statement.

## Where the brief, the DAG or earlier work was wrong

The presentation/idempotent transport in the planned ordinary proof is unnecessary.
Both composite functors are already left adjoints of the same coefficient-restriction
square. The identity-on-sections square is sufficient and preserves the actual units.

The full derived mate route was explored and written in scratch, but not delivered as
proved: its specialized algebraic inverse-image and cochain comparison glue still needs
Lean work. The residual docstring records the derived comparison argument. The
subterminal-section proof of actual unit invertibility has been implemented separately. Empty and terminal opens, zero
modules, identity coefficient maps, and arbitrary nonflat coefficient changes do not
require additional hypotheses in either ordinary proof or residual statement.

## New nodes

`def-pur-topos-open-scalar-section-data`: owns the verbatim section-interface definitions
moved to `Sheaf.CategoryTheory.ToposOpenScalarBasic`; there are no postponed data proofs.

`lem-pur-topos-open-scalar-derived-from-ordinary`: the remaining derived lift of a fixed
ordinary balancing isomorphisms whose generator formulas are supplied and proved by
the parent. It has one public theorem, one sorry, a complete natural-language proof,
and a source reference. The change record is
`coord/changes/r7-topos-open-scalar-section-module.md`.

`lem-pur-topos-open-derived-unit-is-iso`: proves invertibility of the actual open unit,
including its exact-derived normalization, in `Sheaf.CategoryTheory.ToposOpenUnitIsIso`.

`lem-pur-topos-open-scalar-restriction`: proves ordinary scalar/restriction compatibility
and its pure-tensor formula in `Sheaf.CategoryTheory.ToposOpenScalarRestriction`.

## Second reading by R7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
