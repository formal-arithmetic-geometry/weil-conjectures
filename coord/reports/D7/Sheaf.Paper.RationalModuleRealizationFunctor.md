## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.rationalModuleRealizationFunctor` with an
explicit assembly. The completed-to-continuous coefficient isomorphism and finite quotient
isomorphisms are constructed from the existing normalized comparisons. The proof checks
both quotient normalizations, the completed constant-scalar square, the immersion square
and the canonical field action. Integral stratified-perfect cohomology, exact extension
and the natural cohomology comparison then give boundedness and stratified finite local
freeness. The ordinary coefficient model is finite and free after extension to the field.
The normalized field action is returned explicitly by the transport lemma; importing
the larger realization-data module is unnecessary. This also avoids installing its
field-action instances while elaborating the existing public declarations.
After those declarations, four large coefficient/derived functor definitions are marked
locally irreducible for the proof; their exported reducibility is unchanged.
The item compiles in 30.4 seconds, and both new modules compile separately. Profiling
options were removed before delivery; the delivery checks recompile the final files.
Existing definitions, the realization structure and the theorem statement are unchanged.
The two derived theorem commands locally disable the four general integral-operations
sheafification/derived instances, following the existing project proofs, to avoid an
unconstrained auxiliary universe. This setting is scoped to each theorem command.

Separated two remaining coefficient-presentation transport arguments into new theorem
modules. The localization transport supplies exactness, prescribed derived extension,
cohomology and the fixed raw fraction functor. The ordinary local-model transport handles
the two constant-module presentations and their stratum/slice comparisons. Their source
proofs and edge cases are written in their docstrings and DAG nodes. The item's DAG proof
now records this assembly.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.Scheme.rationalModuleRealizationFunctor`
(`lem-per-rational-module-realization-functor`). No holes remain in the item module.

Two holes added, each exactly the body of a named public theorem in its own new module:

- `AlgebraicGeometry.Scheme.rationalModuleLocalizationTransport`
  (`lem-per-rational-module-localization-transport`).
- `AlgebraicGeometry.Scheme.rationalModuleLocalModelsTransport`
  (`lem-per-rational-module-local-models-transport`).

This is a decomposition: one upper hole closed, two strictly smaller transport holes
added, for two actual holes in the delivery. Neither new statement asserts the original
realization datum. In particular the first excludes coefficient construction,
constructibility and ordinary models; the second is independent of derived categories
and raw rationalization and applies to arbitrary stratified finitely presented sheaves.
The coefficient normalization and the combination via cohomology are proved in Lean.

## No longer needed

Removed the item's unused private proof imports:

- `Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction`
- `Sheaf.CategoryTheory.LocalizationInverseImageCoherence`
- `Sheaf.CategoryTheory.ScalarLocalizationSheafExact`
- `Sheaf.CategoryTheory.ScalarLocalizationTriangulated`
- `Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Mathlib.Algebra.Homology.DerivedCategory.Linear`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`

The generic derived-localization and stratum-model nodes remain needed through the two
transport nodes. No module or mathematical argument is withdrawn. All public imports
are retained. The item's obsolete direct tool approvals were reduced to its actual
immersion-restriction and integral-characterization inputs; the other eight generic tool
approvals concern the transport steps and are no longer direct uses of this assembly.

## Where the brief, the DAG or earlier work was wrong

The existing generic inputs do not specialize by just assigning their names to the datum
fields. Derived localization uses another coefficient/derived-adjunction presentation
and constructs a raw shift structure that must be compared with the fixed one. The
stratum-model input uses `constantModuleHomFunctor`, whereas this item specifies
`adicLisseConstantModules` and `integralConstantModule`, as well as inverse-image
coefficient rings before identifying them with the stratum's continuous functions.
These are legitimate mathematical identifications but require nontrivial transport.
The two new statements isolate precisely those missing interfaces. No false statement,
target change or departure from the unit route was found.

The theorem's old docstring listed eight proof steps while the current DAG had already
consolidated them into three. Its docstring now describes the actual assembly.

## New nodes

`lem-per-rational-module-localization-transport`, in
`lean/Sheaf/Paper/RationalModuleLocalizationTransport.lean`, is the completed-presentation
transport of exact derived localization and fraction descent. It retains the original
generic localization theorem and integral characterization as proof inputs. The object
and fraction equations are literal equations in the project's fixed raw category, with
the canonical constant-section field action.

`lem-per-rational-module-local-models-transport`, in
`lean/Sheaf/Paper/RationalModuleLocalModelsTransport.lean`, transports ordinary finite
local models between the completed and continuous presentations and compares constant
module realization. Its proof uses the existing stratum finite-free model theorem,
coefficient restriction and ordinary scalar-extension adjunctions, including rank zero,
torsion and empty-stratification cases. Neither new node duplicates a blueprint node;
semantic searches of the full DAG and blueprint and three kinds of Mathlib searches
were recorded. No shared definition or statement was changed, so no change record is
needed.

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
