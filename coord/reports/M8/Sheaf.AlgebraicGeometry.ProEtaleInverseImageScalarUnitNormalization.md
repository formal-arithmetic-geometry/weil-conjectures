## What changed

Proved `AlgebraicGeometry.Scheme.proEtaleInverseImage_scalarUnit_normalization`
in `Sheaf.AlgebraicGeometry.ProEtaleInverseImageScalarUnitNormalization`.
Its statement, structures, existing definitions and public imports are unchanged.
The two new proof imports expose the proved operation-transport helpers of
`ProEtaleAlgebraicInverseImage` and the proved independent-universe section
calculus helpers in `CochainInverseComparison`. The latter also provides the
cartesian products of set sheaves.

The algebraic presentation explicitly uses the specified module functor and the
existing uniquely unit-normalized underlying ring/module identifications.
The private construction retains their unit formulas. Identity extension of
scalars uses Mathlib's `ModuleCat.extendScalarsId`, module sheafification and its
invertible counit. The presheaf scalar-extension functor gives exactly the
specified `changeOfRingsHom` maps. The sheafification triangle identity gives
multiplication on `1 tensor m`; linearity gives multiplication on `b tensor m`,
and the inverse identity gives insertion of one. The final formula evaluates
the supplied comparison on the unit image of `(s,t)` in the product of the two
underlying set sheaves and then cancels the multiplication isomorphisms.
All added helpers are private and proved; there is no new public declaration.
The tensor-section restriction and naturality formulas reuse the existing
proved `CochainScalarConstruction.pure_restrict` and `pure_map` helpers via a
proof-only `import all`; their pure-section definition is identical to the
recorded `ringedComparisonPure`. The general inverse-image tensor-comparison
theorem of that module is not used.
The section calculation is expressed over generic sites and specialized to the
pro-etale adjunction only at its naturality equation. The private scalar and
tensor helpers reuse their sheafification instances during elaboration.

Updated the item node's proof and dependencies to this argument. Separated the
already existing unit-normalized identification declarations from the larger
parent tensor-comparison node into their own DAG attachment, and updated the
parent and existing algebraic-presentation node accordingly. No Lean source
outside the assigned item is changed, including the F1-held parent module.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.Scheme.proEtaleInverseImage_scalarUnit_normalization`
(node `lem-pur-inverse-image-scalar-unit-normalization`).
The item has zero remaining `sorry`; the delivery adds zero holes and splits
off zero Lean statements. This is a proof from existing stated dependencies,
including the existing `ringSetsIdentification_exists` and
`moduleSetsIdentification_exists` precursor theorems, whose original holes
remain in their original module. They are not newly introduced assumptions.

## No longer needed

No existing import or module is removed. The direct dependency and tool-use
approval for `lem-pc-sites-sheaf-tensor-bilinear-universal` are removed from the
item node: Mathlib's proved identity scalar-extension isomorphism and module
sheafification suffice. That node is not withdrawn; its other users remain.
The finite-limit site-inverse-image tool remains needed by the existing
canonical-identification and operation-transport argument, so its approval is
retained. No unit statement or realized unit proof step is bypassed.

The item uses only precursor declarations from
`Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison`, through the
existing algebraic-presentation module; it does not use the later
`inverseImage_tensor_comparison` theorem or claim that parent module is pruned.

## Where the brief, the DAG or earlier work was wrong

The original scalar-multiplication plan is valid but unnecessary: its
Hom--bilinear universal property is replaced by the existing sectionwise
`ModuleCat.extendScalarsId` and sheafification adjunction.

The parent DAG node attached both its tensor-comparison theorem and the
underlying-identification precursors. A dependency on the latter must be
represented separately, since that parent's tensor theorem itself uses this
normalization item. The new attachment records exactly the existing precursor
statements; their Lean signatures, definitions and proofs are unchanged.
The existing algebraic-presentation node's dependency is corrected to refer
to these same precursors rather than the larger theorem.
The precursor declarations still physically live in the parent Lean module.
The current import graph is acyclic. A future proof in that module which imports
this item will need to separate those prerequisites at the module level; that
refactor is not performed in the other group's held Lean source here.

## New nodes

`lem-pur-proetale-unit-underlying-identifications` attaches the existing
`AlgebraicGeometry.ProEtaleTensorComparison.ringSetsIdentification_exists`,
`ringSetsIdentification`, `moduleSetsIdentification_exists`, and
`moduleSetsIdentification` declarations. These are the unique underlying
identifications normalized by the specified adjunction units. Its source is
Stacks Tags 03D2 and 00YV, as in their existing docstrings. It introduces no
Lean module, theorem, definition or hole. The existing parent attachment
retains all its other declarations. No definition or statement changes and
no forced consumer adaptations occur.
Preflight requests a proof-context record for the additional private helper
sections and local attributes: `coord/changes/M8-scalar-unit-normalization-proof-context.md`.
It records the unchanged public interface and the absence of current Lean importers.

## Second reading by M8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
