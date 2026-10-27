## What changed

Replaced the body of `AlgebraicGeometry.ProEtale.spQbarPositiveRootBasis` by a
categorical colimit argument followed by the existing positive tensor-power
construction. Its statement, coefficient objects and root hypotheses are unchanged.

Private helpers construct a module isomorphism from compatible stage bases, prove
that slice restriction preserves colimits, and transport the resulting internal
module isomorphism to the actual sectionwise slice modules. The linearity proof
uses the defining action of `spQbarTwist`, checked on the diagonal tensor of the
coefficient colimit cocone. It therefore does not replace the prescribed action
by a transported or arbitrary action.

Added the proof-only import `Sheaf.Paper.SpRationalRootDiagramBasis` and private
proof access to the already proved `linePowerOverUnit`. The new module isolates
the normalized rational-stage diagram comparison, before the field colimit and
before positive powers.

Validation: the new module compiled in 41.1 seconds and the item compiled cleanly
in 20.9 seconds through `lcompile.py`. The original theorem signature is identical
to the repository signature. Both files satisfy the 100-character line limit.

## Proved and sorry left

Closed the original textual hole in
`AlgebraicGeometry.ProEtale.spQbarPositiveRootBasis`
(node `lem-sp-qbar-positive-root-basis`) by reduction to a rational-stage diagram
comparison. The colimit transport, its linearity for the actual Qbar action,
section reconstruction and all positive tensor powers are proved in Lean.

Added one hole:
`AlgebraicGeometry.ProEtale.spRationalRootDiagramBasis`
(node `lem-sp-rational-root-diagram-basis`). Its entire proof is `by sorry`, in its
own module with the source and complete proof in words. It asserts only a
compatible family of rational finite-field bases and their stagewise linearity.
It does not mention the Qbar twist, take the field colimit, or assert any positive
power trivialization. This is a decomposition: one original hole closed, one
strictly intermediate hole added, net zero. No other hole remains in the item,
and no helper definition contains a hole.

## No longer needed

None. The original public import and definition dependency
`sk-def-sp-tate-twist` remain necessary. No existing module, declaration or node
is withdrawn. The unit route is retained. Existing separate per-field bases do
not suffice to replace the new compatibility statement.

## Where the brief, the DAG or earlier work was wrong

The old proof step compressed the normalized finite bases, compatibility across
fields, colimit action and arbitrary positive powers into one sentence while
listing only the twist definition. The reduction now distinguishes the missing
rational diagram comparison from the formal colimit and power arguments.
`spIntegralRationalRootBasis` provides individual slice isomorphisms; its statement
does not assert field-transition compatibility, so choosing those witnesses
independently would not justify the colimit argument.

No mathematical statement is disputed and no target statement, shared definition
or existing signature is changed. The unit record has no realized nodes attached
to this item. The new node inherits the blueprint ancestor recorded on
`lem-sp-qbar-root-basis`; the generic ancestor script cannot traverse the older
module-name-valued `created.item` fields.

## New nodes

`lem-sp-rational-root-diagram-basis`, implemented by
`Sheaf.Paper.SpRationalRootDiagramBasis`, isolates the normalized rational bases
compatible with every finite-field inclusion, with their original scalar actions.
Its sources are the explicit field-transition paragraph of
`sec-proetale-coefficients/sk-def-sp-tate-twist/_section.md` and clause (3) of
`sk-def-sp-tate-twist-locally-free.proof.md`, both read under
`literature/blueprint/latest/`. The finite-level formula, inverse-limit comparison,
and scalar extension are stated in existing dependencies. LeanSearch returned
base-change and scalar-tower facts, LeanFinder returned cyclotomic-character
facts, and source/DAG searches found individual bases but no compatible diagram
comparison. Empty slices are included; no nonemptiness, quasi-compactness or
new invertibility condition is introduced. There are no change records because
no existing interface changes.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
