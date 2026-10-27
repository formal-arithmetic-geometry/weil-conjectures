## What changed

Filled `AlgebraicGeometry.Etale.affineCoordinateCounit_baseChange` using the existing
ordered tower adjunction, bounded/unbounded compact-support comparison restriction,
unit compact-support base change, tower counit base change, and uniqueness of normalized
projective-line data. A private generic mate calculation transfers the counit equation
to the actual exceptional comparison.

Filled `AlgebraicGeometry.Etale.exists_coordinateCounitAdjunction`. The prescribed
standard orientation is invertible. Starting from the existing affine-space adjunction,
a natural automorphism of its explicit tensor-and-shift right functor adjusts its unit
orientation to exactly the prescribed map. The categorical normalization is proved in
a general helper module.

The proved auxiliary results `coordinateTowerAdjoint_isIso`,
`coordinateCoefficientUnit_baseChange`, `coordinateUnitPullback_eq_singleConstant`, and
`tensorRightAdjunction_normalize`
are in four new modules, with new DAG nodes.
Profiling after local instance alignment and generic categorical wrappers still put
all the independent calculations in one file over 60 seconds. Moving these
self-contained calculations gives each file its own bounded compile. There are no
unproved auxiliary results. The source-library exceptional counit API is imported from
`WeilOperations`. Local instance priorities retain the recorded derived-category
instances; local irreducibility prevents unnecessary expansion of derived functors.
All existing public signatures,
public imports, definitions, and the previously proved chart-normalization argument stay
unchanged. Added imports are proof-only. The node records the implemented route.

Validation: `lcompile.py --all` compiled all five modules successfully, with no
errors or warnings and with every file passing the per-file check. All four existing
public theorem signatures and the public-import list match the repository verbatim.

## Proved and sorry left

Closed two of the three original holes:

- `AlgebraicGeometry.Etale.affineCoordinateCounit_baseChange`.
- `AlgebraicGeometry.Etale.exists_coordinateCounitAdjunction`.

The four new auxiliary declarations are also proved:

- `AlgebraicGeometry.Etale.coordinateTowerAdjoint_isIso`.
- `AlgebraicGeometry.Etale.coordinateCoefficientUnit_baseChange`.
- `AlgebraicGeometry.Etale.coordinateUnitPullback_eq_singleConstant`.
- `CategoryTheory.tensorRightAdjunction_normalize`.

One original hole remains unchanged:

- `AlgebraicGeometry.Etale.sectionCoordinateCounit_standard`, node
  `lem-trf-section-coordinate-counit-normalization`. Its remaining argument transports
the tower base-change identity through the fixed standard-coordinate and Tate
comparisons, then restricts to the two zero sections and cancels their orientations.

Added holes: zero. Unproved split-off statements: zero. The existing
`AlgebraicGeometry.Etale.sectionCoordinateCounit_normalization` proof is preserved.
The constructions and arguments apply also to dimension zero, empty schemes, and the
zero coefficient ring; no coefficient cancellation or flatness of base change is used.

## No longer needed

No baseline import or module is removed, and no global pruning is claimed. The
parent proof no longer directly needs
`lem-amb-unbounded-compact-support-comparisons`,
`lem-amb-affine-trace-compact-comparison-restriction`, or
`lem-amb-affine-space-top-trace` for tower invertibility, nor directly
`det-sp-unique-right-adjoint` for the affine presentation: it uses the proved
`lem-trf-coordinate-tower-adjoint-isomorphism` and
`lem-trf-tensor-right-adjunction-normalization`. Those dependencies remain needed
transitively. The direct compact-restriction and projection-formula-unit proof imports
introduced during this work now belong to the respective auxiliary modules. The proof
uses the existing compact-comparison restriction and unit-base-change declarations to
avoid rebuilding the unbounded compact-support coherence argument. The dependencies
for the remaining
standard-pair hole and the previously proved chart clause are retained.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. For the existence of a normalized affine adjunction,
the planned explicit transport of the entire coordinate tower is unnecessary: the
existing affine adjunction can be adjusted by tensoring with a coefficient automorphism.
The DAG proof and proof dependencies now describe that shorter argument. The remaining
standard-pair hole still needs the coordinate/Tate coherence in its original plan.

## New nodes

`lem-trf-coordinate-tower-adjoint-isomorphism`, realized by
`Sheaf.Paper.CoordinateTowerAdjointIsIso`, proves the isomorphism part of the tower
base-change conjunction. It uses the existing compact-comparison restriction and
counit-compatible uniqueness of right adjoints. Its proof is complete; it adds no hole.

`lem-trf-coordinate-coefficient-unit-base-change`, realized by
`Sheaf.Paper.CoordinateCoefficientUnitBaseChange`, proves the canonical coefficient-unit
identity needed in transferring the tower trace equation to the derived coefficient
unit. It is strictly a coefficient-comparison calculation, with no trace or exceptional
mate in its statement. Its proof is complete; it adds no hole. No change record is
needed: no existing signature, definition, public import, or global attribute changes.

`lem-trf-coordinate-single-constant-pullback-comparison`, realized by
`Sheaf.Paper.CoordinateSingleConstantPullbackComparison`, identifies the cached
constant-coefficient pullback isomorphism with the canonical derived one. It is proved
using the published cached-functor equalities, evaluation of natural isomorphisms, and
associativity. The coefficient-unit module uses this result. These two proofs each
passed kernel checking in the combined version, but together exceeded 60 seconds;
they are separated so each can be checked within the per-file limit. This node adds
no hole.

`lem-trf-tensor-right-adjunction-normalization`, realized by
`Sheaf.CategoryTheory.TensorAdjunctionNormalization`, is the proved categorical
normalization argument for a right functor of the form pullback, tensor, and a fully
faithful endofunctor. It constructs the required natural automorphism and transports
the adjunction. The item now specializes this theorem to the Tate tensor and even
shift. This final extraction follows a compiling 62-second item check and brings the
concrete file below the limit. It adds no hole.

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
