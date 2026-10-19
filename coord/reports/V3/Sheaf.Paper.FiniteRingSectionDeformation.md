## What changed

Completed eleven proofs in `lean/Sheaf/Paper/FiniteRingSectionDeformation.lean`, keeping
all declaration signatures, definitions, visibility and imports unchanged. The main
conclusion now combines the existing geometric, line, fibre and unique-comparison
statements. The specialization proof uses invertibility of the prescribed zero-fibre
map and functorial preservation of isomorphisms.

The geometric proofs identify the actual extended-Rees base-change map as Cartesian
using the published affine Rees pushout cover. Pullback pasting gives the induced
normal-cone square; the zero sections agree by the pullback universal property.
The etale-pair ideal bound follows directly from the commuting centre square. The
coordinate deformation chart uses etaleDeformationMap_spec and the standard affine
Rees isomorphism. Projection and bundle-frame zero identities use the actual coordinate
and augmentation maps.

Validation: the full module compiled through lcompile.py. The resumed delivery dry run
compiled and probed all 70 declarations. After wrapping its one reported line over the
100-character limit, the current-source dry run passed at commit `26a5bc4760`, with
review class AUTO. No new holes, signature changes or definition changes were reported.

## Proved and sorry left

Closed 11 of the original 22 holes; added 0 holes and split off 0 statements.
The proofs still depend on the existing named theorem obligations listed below.

Proved (all in `AlgebraicGeometry.Etale.FiniteRingSectionDeformation`):

- `isIso_specialization`.
- `baseChange_geometry_exists`.
- `baseChange_geometry`.
- `etalePair_ideal`.
- `etaleDeformationMap_spec`.
- `etaleNormalMap_condition`.
- `coordinateDeformationMap_spec`.
- `coordinateTower_over`.
- `standardZero_over`.
- `bundleFrame_zero`.
- `finiteRingSectionDeformation`.

The following 11 declarations retain their original whole-proof `sorry`, with their
original source and complete proof docstrings. All belong to
`lem-trf-finite-ring-section-deformation`:

- `geometry`.
- `coneBundleIso_spec`.
- `lines_and_fibres`.
- `existsUnique_normalized`.
- `baseChange_compatibility`.
- `etaleNormalMap_spec`.
- `etale_compatibility`.
- `coordinate_normalization`.
- `bundleAdjoint_isIso`.
- `bundleOrientation_frames`.
- `bundleOrientation_purity`.

The remaining geometry theorem needs the regular-coordinate/conormal construction.
The line theorem needs exact pullback of local free rank-one trivializations and smooth
exceptional base change. The normalized comparison needs the local construction and
connected-fibre uniqueness/gluing argument. The remaining comparison and orientation
theorems need their stated counit/mate-pasting and augmentation calculations.

## No longer needed

None. No imports, modules or nodes were removed: the remaining eleven obligations still
use the original dependency plan. No new proof-dependency import or node was introduced.
The unit route is unchanged; the completed proofs implement its existing geometric and
formal-combination steps using the published construction APIs.

## Where the brief, the DAG or earlier work was wrong

At session start the local shared checkout lacked this module although its node and
queue entry existed. The reviewed 980-line module was available on the project server;
that exact version was copied to the sandbox and compiled before editing. The local
shared checkout subsequently acquired the module with one additional private exactness
import, which this delivery preserves. There is no statement or
definition repair in this delivery.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
