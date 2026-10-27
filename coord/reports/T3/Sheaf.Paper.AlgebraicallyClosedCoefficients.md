## What changed

Filled all 15 original theorem holes in
`lean/Sheaf/Paper/AlgebraicallyClosedCoefficients.lean`, using the proved upstream
StageSystem quotient, additive morphism and shift APIs, and Mathlib's abelian-group
direct limit. The Hom-coordinate equivalence is constructed in both directions.
The original transported Hom groups are retained and proved equal to the native
quotient groups. The cone proof conjugates a stage image triangle by its canonical
stage isomorphisms.

Constructed the shift and inclusion comparisons from the actual upstream data.
The tensor associator uses direct equality transport at the coefficient-map level;
a proved equality identifies it with the original tensor formula. The sealed
associator specification fixes its entire isomorphism by equality. The stage-system
projection API and direct instance caches avoid unfolding the completed sheaf
construction during elaboration. Added the fully proved normalized associator shift
compatibility module. Definition changes and consumer checks are recorded in
`coord/changes/algebraically-closed-stagewise-shift.md`.

## Proved and sorry left

Closed these original holes, all in
`WeilConjectures.AlgebraicallyClosedCoefficients` and attached to
`def-weil-algebraically-closed-coefficients`:

- `coefficientInclusion_laws`
- `associator_cocycle`
- `stageSystem_existsUnique`
- `stageTransition_exact`
- `stageTransition_additive`
- `transport_additive`
- `homCoordinates_existsUnique`
- `composition_bilinear`
- `inclusion_additive`
- `representatives`
- `shift_exists`
- `zero_exists`
- `transitionIso_commShift`
- `distinguished_iff`
- `commonStage_cone`

Added zero holes. No sorry remains in either delivered Lean module. The new
`WeilConjectures.rationalConstructibleScalarComp_commShift` theorem and all its
helpers are proved. This is proof completion, not decomposition.

Validation: `lcompile.py --all` compiled both delivered modules, all five direct
consumers (`CoefficientTwistsDetailed`, `ConstantCoefficientObjectsConstructible`,
`ConstructibleStandardTStructure`, `SfAlgebraicallyClosedCoefficients`,
`SitePerfectComplex`) and the transitive `GeneralAlgebraicallyClosedCoefficients`
interface, with exit code zero and no warnings. The six unchanged validation copies
were removed from the delivery. All 15 original written theorem signatures are
unchanged. No whole-library build was run by this worker.

## No longer needed

No statement node, project module or unit step is withdrawn. The upstream
StageSystem quotient supplies representatives and their equality criterion, and
its additive morphism API supplies shift additivity. No separate reconstruction of
those arguments or new holed intermediate theorem is needed. No original import
is removed. The upstream preadditive API remains a proof-only import. No project
dependency is pruned.

## Where the brief, the DAG or earlier work was wrong

The owning node's current Lean attachment is the intrinsic General interface; this
assignment is its retained finite-field legacy module. The delivery preserves that
attachment. Its proof record preserves the current intrinsic proof steps and
appends this legacy realization explicitly. The current unit route is preserved.

The former arbitrary choice of shift coherence data from `shift_exists` was
unnecessary. The proved upstream construction provides exactly the displayed
stagewise action and normalized inclusion comparisons. The specified transported
Hom group equals the native quotient group. Keeping the upstream preadditive API
private preserves the existing instance selection in other modules; the proved
group and preadditive equalities transfer its proof APIs.

## New nodes

`lem-weil-scalar-associator-shifts` records the fully proved compatibility of the
normalized tensor associator with every integer shift. Its proof restricts the
ordinary derived associator, transports its square through rationalization on pure
tensors, extends degree one to all integers, and conjugates by the normalized
completion comparisons. It adds no sorry. The associated definition change record
is `coord/changes/algebraically-closed-stagewise-shift.md`.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
