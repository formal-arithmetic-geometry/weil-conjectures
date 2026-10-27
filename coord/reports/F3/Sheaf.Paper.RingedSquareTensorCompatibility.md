## What changed

Replaced the proof hole in `SheafOfModules.ringedSquareTensorCompatibility` by the
representative calculation described in its existing docstring. The statement,
universes, public import, and square data are unchanged. Proved helpers establish preservation of the
representative class, invertibility and naturality
of the complex comparisons, the canonical edge equation, and its composition for
two edges. The final proof cancels invertible representative identifications and
reduces both sides to localization of the ordinary total-complex square.

Added `Sheaf.Paper.RingedSquareOrdinaryTensorCompatibility`: it extends ordinary
module compatibility to total complexes by checking every coproduct summand,
using naturality of the module square, and conjugating by the total comparison
isomorphisms. Added `Sheaf.Paper.RingedSquareModuleTensorCompatibility` for the
remaining ordinary module-sheaf generator calculation. This statement has no
complexes, derived categories, tensor models, representative hypotheses, or theta.

The proved `Sheaf.Paper.RingedTensorEdgeRepresentativeEquation` extracts the
canonical edge equation into its own compilation unit. This avoids repeating
the expensive unique-characterization elaboration in the item module. It adds
no hole. The proved component formula and hom-oriented total square are separate
modules
`Sheaf.Paper.RingedTensorTotalComponent` and
`Sheaf.Paper.RingedSquareOrdinaryTensorHomCompatibility`, keeping each part
within the per-file compile limit. All changes are in the item, its node, and new
modules and nodes. No shared
interface, source-library declaration, definition, or target statement changes.

Validation: all six modules compiled through `lcompile.py`, including the final
derived proof after removing intermediate rewrite reflexivity checks. The final
item check took 58.2 seconds. Profiling options and the temporary probe were removed.

## Proved and sorry left

Closed one original hole: `SheafOfModules.ringedSquareTensorCompatibility`
(`lem-weil-pbc-ringed-square-tensor-compatibility`).

Proved the new `SheafOfModules.ringedSquareOrdinaryTensorCompatibility`
(`lem-weil-pbc-ringed-square-ordinary-tensor-compatibility`), `SheafOfModules.ringedTensorEdgeRepresentativeEquation`,
`SheafOfModules.ringedTensorTotalComponent`, and
`SheafOfModules.ringedSquareOrdinaryTensorHomCompatibility`, with all private helpers.

Added one hole, the only remaining sorry in the packet:
`SheafOfModules.ringedSquareModuleTensorCompatibility`
(`lem-weil-pbc-ringed-square-module-tensor-compatibility`). Its docstring and node
give the pure-tensor insertion argument and its source. This is a decomposition:
one original hole closed, one strictly lower hole added, net zero holes closed.
The item module itself has zero sorry.

## No longer needed

Removed the original proof-only imports
`Sheaf.CategoryTheory.ModulePullbackTensorIso` and
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
The former's existential construction is not used: the square edges already
supply their canonical comparisons. Accordingly the old direct dependency
`lem-weil-pbc-ringed-topoi-module-pullback-tensor` is removed from the item node.
The latter's independent-universe tensor-comparison construction is not needed:
these corners have small sites in a common coefficient universe, and the original
small-site canonical comparison theorem supplies the edge equation directly.
Its comparison-invertibility result is imported through the narrower
`Sheaf.Paper.DerivedPullbackRepresentativeComputation` module.

The ordinary tensor, flat pullback, and canonical derived tensor dependencies
remain needed. No module is withdrawn and no source-library declaration is
removed. These are route-specific unused dependencies, not a claim that no other
part of the project uses those modules.

## Where the brief, the DAG or earlier work was wrong

The original dependencies provide individual edge comparisons but do not state
tensor compatibility for an arbitrary specified module square. That missing
local calculation is now separated from its fully formalized total-complex and
derived transports. There is no statement dispute.

The proof additionally uses `lem-pur-kflat-total-tensor-model` as a generic tool:
it supplies K-flatness and flat terms for the ordinary total tensor so that
htheta applies there. This preserves the proper-base-change unit's route.
The item also records `lem-weil-pbc-kflat-tensor-pullback-computation-universes`
for invertibility of its specified complex-to-derived comparisons. Local
irreducibility attributes keep large canonical constructions out of categorical
rewrites; no exported attribute changes.

## New nodes

`lem-weil-pbc-ringed-square-module-tensor-compatibility` states the ordinary
module-sheaf tensor square, the remaining local generator calculation. Checked
against zero modules, zero rings, and nonflat structural maps; none requires an
extra hypothesis. Its natural-language proof follows the pure-tensor
normalization and square insertion equation.

`lem-weil-pbc-ringed-square-ordinary-tensor-compatibility` is the proved extension
to arbitrary cochain complexes before localization. The proof uses coproduct
summands and preserves their bidegrees, so there is no additional sign and no
flatness hypothesis. No change records are required.

`lem-weil-pbc-ringed-tensor-edge-representative-equation` is a proved extraction
of the canonical comparison characterization. It takes the target preservation
proofs explicitly, so its statement depends only on the original comparison API.
It is separated for the 60-second compilation limit, not an additional hole.

`lem-weil-pbc-ringed-tensor-total-component` proves the canonical comparison
formula after precomposing with one coproduct inclusion.

`lem-weil-pbc-ringed-square-ordinary-tensor-hom-compatibility` proves the
degreewise square in the hom orientation. The ordinary compatibility module
then performs only the categorical inversion. Both are fully proved support
modules extracted for compilation time; neither introduces a hole.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
