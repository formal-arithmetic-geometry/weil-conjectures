## What changed

Replaced the sole hole in `Sheaf.Paper.DiagonalTraceGeometricModelExistence` by a
complete assembly from two strictly smaller ordinary sheaf constructions. The
original theorem signature and public import are unchanged.

Added `Sheaf.Paper.TowerClassTensorPullback`, a concrete API for the existing
ordinary sheaf tensor and its adjoint-normalized inverse-image comparison. Added
`Sheaf.Paper.TowerClassTensorGeometryExistence` and
`Sheaf.Paper.TowerClassLinePullbackExistence`, each containing one named remaining
construction theorem. The first contains no Chern data, root line, twisting, or
projective model. The second only identifies the root line for an already
normalized geometry; it contains neither positive-twist transport nor projection.

The item's proved private helpers construct tensoring with a line isomorphism,
prove its pure-section formula, construct positive-twist pullback and prove its
normalization using `sectionAdjoint_postcomp` and the explicit-carrier
`sectionAdjoint_heq` bridge. Local unfolding controls avoid reducing the full
direct-image carriers while comparing heterogeneous sections. The final helper identifies the
specified projection with the right adjunction mate and proves invertibility
from the two derived twisting equivalences. Thus no new hole asserts a Model or
restates the full original obligation. All selected data are used inside theorem
proofs; no definition chooses an arbitrary witness of a holed existence theorem.

Updated the item's proof route and added three matching nodes. Proof imports are
private. No existing module besides the assigned item was changed.

Validation: all four modules compiled remotely through lcompile.py. The final
assembly took 26.1 seconds in the diagnostic run. Profiling options were removed
afterward. The explicit-carrier tensor API compiled without warnings, as did both
remaining construction statements. The original theorem signature was checked
verbatim against the shared source; no line exceeds 100 characters.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.DiagonalTrace.exists_diagonalTraceGeometricModel`.
The item's positive-twist construction, its section normalization, and the
projection invertibility helper are fully proved without local holes.

Added two holes, each exactly `:= by sorry` in its own module:

- `AlgebraicGeometry.ProEtale.SpTowerClasses.exists_tensorGeometry`
  (`lem-sfb-tower-class-tensor-geometry-existence`): choose actual tower geometry
  with normalized coefficient-unit and ordinary tensor comparisons.
- `AlgebraicGeometry.ProEtale.SpTowerClasses.linePullback_nonempty`
  (`lem-sfb-tower-class-line-pullback-existence`): assemble the coefficient/root
  finite comparisons to the prescribed ordinary Tate-line comparison.

This is a decomposition: one upper hole closed, two lower holes added, zero holes
left in the item, two holes in the delivered files. It is not a net hole reduction
or a claim of an axiom-free target proof. The tensor API contains no holes.

## No longer needed

No original public import was removed and no module is withdrawn. No global
module pruning is claimed.

The original direct proof dependency on `lem-pur-twist-sheaf-locally-free`
(`Sheaf.Paper.PurTwistSheafLocallyFree`) is unnecessary for the projection step:
the input Twisting records already give equivalences, and the generic mate theorem
proves invertibility. Finite root/cartesian facts are still needed by the line
construction, so their dependencies are not claimed to be globally pruned.

The original coefficient-tower and semilinear-calculus dependencies
(`det-sp-coefficient-towers-abelian`, `lem-coef-semilinear-derived-sections`) belong
to the remaining ordinary geometry construction, not to an additional duplicate
construction in the combining theorem. The pullback and twisting definitions
remain used. No scalar-restriction, limit-comparison, cohomological-splitting,
or trace theorem is imported by the new proof.

## Where the brief, the DAG or earlier work was wrong

The original proof plan suppressed the coherence needed to construct the
coefficient unit and root-line maps as actual ordinary system morphisms. Merely
having finite evaluation comparisons is not a supplied theorem establishing
those normalized morphisms. The new geometry lemma therefore chooses normalized
coordinates as part of its construction, rather than assuming the normalization
for every arbitrary geometry record.

Projection invertibility does not require proving local freeness again: the
Twisting arguments already contain exactly the equivalences needed for the mate
argument. This observation eliminates the final categorical obstruction instead
of moving it to another existence theorem. No existing statement was changed or
marked disputed; the unit route is unchanged.

## New nodes

`def-sfb-tower-class-tensor-pullback` records `tensorRight`, `tensorPure`, and
`TensorPullback` on the existing ringed sequence sites. It is a definition with
actual tensor data, not a holed construction.

`lem-sfb-tower-class-tensor-geometry-existence` isolates the coefficient-unit and
ordinary tensor part of the geometric realization. Its plan uses the existing
strict-system geometric realization, semilinear calculus, and `semilinearGeometryOrdinary` /
`geometricOrdinaryTensor_exists`. Their explicit ordinary, naturality and
finite pure-tensor fields should be reused for the remaining assembly. These are generic construction tools,
not a different route around the diagonal-tower unit.

`lem-sfb-tower-class-line-pullback-existence` isolates the root-line comparison.
Its plan uses `spRoots_cartesian` and `spFiniteTwists_cartesian` from
`det-prop-sfb-cartesian-coefficients-twists`, then ordinary scalar extension and
horizontal compatibility. These finite Tate comparisons are the needed generic
tool from the coefficient-twist unit. The Chern/twisting/model declarations of
the original unit remain in use.

Mathlib searches (LeanSearch, LeanFinder/Loogle, and grep), plus searches of the
local library and imported blueprint, found no existing theorem of either exact
normalized ordinary-tower construction. The existing finite root/Tate comparison
and generic mate theorem were retained instead of restating them. Edge cases
checked in the mathematical statements: empty schemes/charts, the zero finite
quotient ring, positive indexing n+1, ramified coefficients (no flatness of
quotient transition maps), and arbitrary f. There is no need for a global basis
of the root line. The change record `coord/changes/J8-diagonal-trace-local-attributes.md` explains
the module-local unfolding controls and confirms the existing imported interface
is unchanged. The first preflight signature-record mismatch was corrected by
recording the structure header in the format used by the signature reader.

## Second reading by J8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
