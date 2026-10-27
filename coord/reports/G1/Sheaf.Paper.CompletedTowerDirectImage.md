## What changed

Discharged `completedDirectImageProjectionFormula_properties` from the existing
perfect tensor projection formula and one new scalar-to-tensor normalization theorem.
The assigned module constructs the comparison of the restricted finite-ring unit
with the constant-system quotient and identifies the explicit derived units with
the generic complex units. A fully proved helper applies perfectness, cancels the
comparison isomorphisms and reflects isomorphisms through exact derived scalar
restriction using homology.
Naturality is proved directly from adjunction naturality and the scalar unit.

The only existing Lean file changed is the assigned item. Every existing definition,
instance, declaration signature and public import stays verbatim. The new proof
imports are private. The new module
`Sheaf.Paper.CompletedScalarProjectionTensorComparison` uses the existing generic
ringed direct-image API and takes the already proved invertibility of the completed
coefficient map as an explicit instance argument. The ordinary direct-image functors
are passed with their defining equalities, and their exact presentations are retained
when deriving; this avoids expensive conversion of chosen localization constructions.
It does not import the item.
No source-library file or target statement is changed. No consumer adaptation is
needed because no existing interface changes.

Validation: lcompile.py accepts all four delivered modules with the normal per-file
limit and no compiler diagnostics.
The first delivery recheck exceeded the 60-second limit (67 seconds), so the explicit
complex-unit calculation is now proved once for abstract additive functors in
`Sheaf.CategoryTheory.RightDerivedComplexUnitNormalization` and reused at both rings. Declaration-local
`Elab.async false` schedules the derived-comparison and assembly checks sequentially;
no transparency
or checking limit is changed. The original definitions, theorem signatures and public
imports compare textually with the source item, and leanindex reports no interface
changes. All node statements match their Lean declarations and their proof dependency
lists equal the unions of the dependencies used by their proof steps.

## Proved and sorry left

Closed the item's single original hole:
`AlgebraicGeometry.Scheme.completedDirectImageProjectionFormula_properties`.
There are zero holes left in the item. Also proved the new public helpers
`CategoryTheory.Functor.rightDerivedComplexUnitNormalization` and
`AlgebraicGeometry.Scheme.completedScalarProjectionPerfectIso`; neither adds a hole.

Added one hole:
`AlgebraicGeometry.Scheme.completedScalarProjectionTensorComparison`, in
`Sheaf.Paper.CompletedScalarProjectionTensorComparison`, node
`lem-pbc-completed-scalar-projection-tensor-comparison`.
It is a named public theorem with a source and complete proof in words.
Its arbitrary compatible coefficient maps have no perfectness hypothesis, and its
conclusion identifies the specified scalar and tensor arrows, without claiming that
either projection is invertible. The parent constructs its finite quotient input,
supplies perfectness and proves invertibility by cancellation and conservativity.
This is a decomposition: one existing hole closed and one strictly smaller
normalization obligation added. It is not a claim of net closure progress against
the imported-dependency baseline. Naturality and all assembly glue are proved in Lean.
No definition contains a hole or chooses data from the new unproved theorem.
Imported pre-existing obligations are retained and are not counted as closed.

## No longer needed

No existing node or module is withdrawn or pruned, and no original import is removed.
The proof uses `PerfectProjectionFormula` instead of duplicating its finite-free,
shift, cone and retract closure development. Its existing tensor projection and
perfectness obligations remain needed. The comparison module publicly imports only
what its statement needs: completed pullback/coefficient data, the generic ringed
restriction/direct-image API, the tensor projection API and right-derived complex units.
The item privately imports a fully proved scalar-projection perfectness helper
(which imports the comparison) and the proved generic unit-normalization lemma.

## Where the brief, the DAG or earlier work was wrong

The original finite projection-property theorem cited
`prop-weil-pbc-direct-image-limits`, whose Lean attachment is the separate
`CompletedDirectImageLimits` interface. The only node attached to this item was a
completed-module-direct-image definition. Added a precise node for the existing
projection-property conjunction; the definition node and the other interface stay
unchanged. The new nodes belong to this theorem's proper-base-change source unit.

The tensor projection theorem uses a limit of constant finite quotient sheaves,
whereas the item uses continuous finite-function sheaves. The canonical system and
limit comparisons identify these presentations; they are not silently treated as
a discrete completed constant sheaf. The new comparison states the normalization
of the actual scalar-adjunction mate and its derived units. The parent explicitly
constructs the finite quotient module identification. No nonzero quotient,
flat quotient or boundedness assumption is added; n=0, the zero quotient and the
empty site use the same limit-projection and tensor-unit equations.

## New nodes

`lem-pbc-completed-scalar-projection-tensor-comparison` records the generic
normalization obligation. This is not invertibility restated with new hypotheses:
it applies to arbitrary compatible target coefficient sheaves and identifies
specified arrows even when those target modules are not perfect. The existing
coefficient-change and tensor-descent declarations do not state this mate equality.
Its source proof uses balanced tensors, K-flat representatives, the tensor-pullback
comparison, and the derived-unit normalization.

`lem-pbc-completed-direct-image-projection-properties` attaches the existing
conjunction to its actual declaration and records the complete assembly proof.
Its dependencies name the new comparison, the existing perfect projection formula,
and scalar restriction. The blueprint unit route is retained.

The comparison plan cites `lem-cbc-extension-tensor-comparison-independent` as a
generic coefficient-change tool: it gives the extension/tensor normalization used
before identifying the two mates. The proper-base-change unit has the tensor
projection and its perfectness theorem, but no declaration equating it with this
scalar mate. No maintainer tool approval is added or changed by this delivery.

`lem-pbc-right-derived-complex-unit-normalization` records a fully proved identity-factor
calculation for arbitrary additive functors. It adds no hole and avoids repeating
this localization calculation with large concrete sheaf-category instances.

`lem-pbc-completed-scalar-projection-perfect-iso` records the fully proved perfectness,
cancellation and conservative-restriction part of the argument. Its module imports
the comparison theorem and proves invertibility from it and the existing tensor
projection theorem. This self-contained proof is compiled separately after first
removing the costly functor-presentation conversions and repeated unit calculations.
It adds no hole.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
