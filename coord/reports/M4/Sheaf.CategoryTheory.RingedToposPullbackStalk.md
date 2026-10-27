## What changed

Replaced the proof hole of `CategoryTheory.RingedToposMorphism.pullback_stalk`
by a reduction to the scalar-extension comparison at one point. The original
statement, definitions, docstring and public imports are preserved.

The private `stalkPresentation` uses the concrete finite-product ring/module
transport and structural-map bundling already proved in
`Sheaf.SecSmoothPurity.CochainCompositeAlgebraic`. It reuses the proved private
`ringImage`, `algebraicImage` and `structuralMap` helpers through `import all`;
it does not apply the composite-existence theorem to missing input lifts. The private `compositePoint`
constructs the composite point presentation with the transported coefficient
ring and composite module functor. Its operation graphs, natural underlying
isomorphism and additivity are proved directly.

The assembly evaluates the point scalar-extension comparison at `I.modules.obj M`,
identifies its coefficient map with the stalk of `f.ringMap`, and cancels the
module underlying isomorphism to prove the specified pure-tensor normalization.
The differential equation is naturality applied to each differential.

Added `Sheaf.CategoryTheory.RingedSitePointScalarExtension`, containing the
remaining tensor step, and updated the item's proof plan to match this route.
The statement of the new lemma has no morphism of ringed topoi, no inverse-image
module construction, no composite point and no complex. It states the point
comparison for extension of scalars along a morphism of ring sheaves on one site.

Validation: `lcompile.py --all` passed for both modules without errors or warnings.
The item compiled in 34.1 seconds, within the unchanged 60-second limit; the new
statement module also compiled successfully. Original public imports and the
original theorem signature were checked verbatim against the shared source.

## Proved and sorry left

Closed the original hole of
`CategoryTheory.RingedToposMorphism.pullback_stalk`
(node `lem-sfb-ringed-topos-pullback-stalk`) by a complete assembly proof.

Added one hole:
`CategoryTheory.RingedSitePoint.scalarExtension`
(node `lem-sfb-point-scalar-extension`), in its own new module, with a source and
complete proof in words. It comprises the point tensor comparison and its scalar,
naturality and generalized-section normalizations, which were steps 3 and 4 of
the original plan. There are no other holes in this delivery and no holes in
any definition or private helper.

This is a decomposition, not a net proof: one upper hole closed, one strictly
simpler lower hole added, net zero. The inverse-image presentation, composite
point, normalization transport and differential assembly are proved in Lean.

## No longer needed

Removed the direct proof imports of
`Sheaf.SecSmoothPurity.CochainInverseComparison` and
`Sheaf.CategoryTheory.GeometricModuleConstruction` from the item. The latter remains
imported by the concrete algebraic-image construction. The former remains a
planned proof dependency of the new scalar-extension node; its module is not
imported into the new statement-only file. No mathematical dependency is claimed
as pruned.

The direct proof-dependency edges to
`lem-pur-independent-inverse-image-tensor-comparison` and
`lem-weil-pbc-geometric-module-construction` are replaced respectively by the
scalar-extension node and the existing concrete-composite construction node.
The former dependencies remain below those nodes. The definitions and size
conventions remain used through the unchanged public interfaces.

## Where the brief, the DAG or earlier work was wrong

The tensor comparison API is stated between two sheaf categories. A topos point
has inverse image with target `Type u`. Applying the API at a point also requires
transport through the one-object-site presentation of Set and identification of
its module tensor with the ordinary tensor. This bridge, together with the
scalar-action compatibility, is now explicit in the new scalar-extension node.
There is no disputed mathematical statement and no departure from the unit route.

The new node uses `lem-pur-independent-inverse-image-tensor-comparison` from
`sk-def-purity-conv` as a tool for the tensor step. The original item already
records that tool approval; the new point bridge supplies the missing Type-valued
case, rather than an alternative proof of the unit. No node of this unit states
that normalized inverse-image tensor comparison. The concrete-composite module
also supplies proved construction helpers from that unit. Existing approvals
are preserved; no maintainer approval entries were added by this delivery.

## New nodes

`lem-sfb-point-scalar-extension` records the point scalar-extension comparison,
with coefficient-map normalization, linearity, naturality and the universal
pure-pairing equation. Its source is Stacks Project, Modules on Sites, Tags 05V5
and 03EL. The proof uses the existing normalized inverse-image tensor comparison
on the one-object-site presentation of Set and tensor symmetry. Edge cases of
zero rings, zero modules and the empty site are included in its proof discussion.
Searches with LeanSearch, LeanFinder, Loogle and Mathlib grep found no matching
arbitrary-topos-point comparison. Blueprint searches for `stalk tensor`, `05V5`
and `scalar extension stalk` found no imported blueprint duplicate.

Change record: `coord/changes/M4-pullback-stalk-proof-support.md`.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
