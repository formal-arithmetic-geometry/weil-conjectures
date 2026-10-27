## What changed

Kept the signature and public imports of
`exists_normalized_pullback_frame_atlas` unchanged. Its proof now uses the
cross-tensor relation of the two quotient maps rather than constructing and
comparing transition fractions directly.

The private argument in the item is general: for epimorphisms q:M→P and q′:M→Q
to invertible module sheaves, a cross-tensor relation produces common lifted
frames. Local lifts of separate frames give q(n)=c q(m) and q′(n)=c q′(m).
Writing q′(m)=a q′(n) gives ca=1; hence q′(m) is a frame too. Cancellation
with q(m) then proves every coefficient identity and overlap relation required
by the unchanged statement. The cover is indexed by the points of the scheme,
so its universe and the empty-scheme case are preserved.

Added `SymmetricProjPullbackQuotientCrossTensor`, with a complete Lean proof
extending the relation from pulled affine generators to all local sections.
It uses the existing bijective affine tensor-section comparison, two tensor
inductions, scalar commutation, affine refinements, and sheaf separatedness.

Added `SymmetricProjPullbackGeneratorCrossTensor` for the remaining geometric
calculation, restricted to two specified pulled generators on an affine open.
It asserts no free frames, atlas, line isomorphism, arbitrary-section formula,
or transition relation. Its docstring explains the standard-open fraction
calculation, including normalization and pullback-composition transports.

All helpers in the item and the arbitrary-section module are proved. Only the
new generator theorem is left with `sorry`. The three DAG records reflect this
route. No existing module other than the item was changed.

Validation: all three modules compiled in import order. The arbitrary-section
module took 8.7 seconds, and the final atlas proof took 18 seconds after replacing
repeated dependent local aliases by an explicit application of the generic helper.
Profiling options were removed. The final delivery reruns compilation and preflight.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.SymmetricProjTautologicalCharts.exists_normalized_pullback_frame_atlas`
(node `lem-trf-symmetric-proj-quotient-pullback-comparison-local`).

Proved the new arbitrary-section theorem:
`AlgebraicGeometry.SymmetricProjTautologicalCharts.normalized_pullback_cross_tensor`
(node `lem-trf-symmetric-proj-pullback-quotient-cross-tensor`).

Added one hole:
`AlgebraicGeometry.SymmetricProjTautologicalCharts.normalized_pullback_generator_cross_tensor`
(node `lem-trf-symmetric-proj-pullback-generator-cross-tensor`).

The item has zero holes, and the delivery adds one named hole elsewhere.
This is a decomposition of one original hole into one strictly smaller geometric
identity, with the affine extension and atlas construction completed in Lean.
The net hole reduction is zero; this is not an unconditional proof of the original
target closure.

## No longer needed

No original import was removed and no module is withdrawn or globally pruned.
The existing two public imports remain verbatim. New imports of the item are
private proof imports.

The item no longer directly needs the old geometric proof dependencies
`lem-nagata-affine-proj-scalar-extension`, `def-weil-pbc-proj-twisting-sheaf`,
`def-nagata-homogeneous-localization-degree-zero`,
`lem-weil-pbc-proj-graded-module-sheaf-exists`,
`lem-weil-pbc-symmetric-algebra-graded`, `prop-nagata-proj-standard-open`,
`lem-weil-pbc-affine-opens-basis`, `lem-weil-pbc-proj-basic-open-intersection`,
and `lem-weil-pbc-module-pullback-affine-sections`.

Scalar extension, homogeneous fractions, symmetric grading, standard opens,
and affine refinements remain in the generator calculation's plan. The affine
module section comparison and affine refinements are used by the proved
arbitrary-section theorem. The basic-open intersection theorem and the
existence of the graded-module sheaf are not separate steps of this route;
any transitive uses in adopted twist or normalization modules remain intact.
These dependency changes do not authorize deleting any adopted declaration.

## Where the brief, the DAG or earlier work was wrong

No false statement or changed hypothesis was found. The original DAG's explicit
simultaneous frame and transition construction is unnecessary once the degree-two
relation is known: epimorphy, invertibility and tensor cancellation supply it.
This does not claim that the remaining geometric identity was already available.

The library search found an affine graded quotient twist comparison, but its
public statement assumes a surjective graded map. General scalar-extension maps
here need not be surjective. Its internal general twist-map proof is useful
background, not an applicable public theorem with the required relative-chart
normalizations. The proved `lineQuotient_pulled_chart_normalization` gives a
usable existing fraction formula for the remaining generator lemma.

The blueprint ancestor command returned no ancestor for the item's immediate
split-node record. For the new nodes, the full historical ancestor and route were
read from its parent `lem-trf-symmetric-proj-quotient-pullback-comparison` and
preserved. Searches of the current imported blueprint for cross tensors and
symmetric pullbacks found no duplicate statement. The unit route is unchanged.

## New nodes

`lem-trf-symmetric-proj-pullback-quotient-cross-tensor` states the degree-two
identity on arbitrary local sections and is proved from the generator identity
by the existing affine pullback section comparison and sheaf separation. It
realizes only the bilinear extension step of the old proof, before the proved
common-frame construction.

`lem-trf-symmetric-proj-pullback-generator-cross-tensor` states only the
cross-tensor identity for two actual pulled affine generators. It isolates the
homogeneous fraction computation of Stacks Constructions 01N2/01NQ, with the
01NR/01OB quotient normalization. On a standard open the two coefficients are
respectively the same pulled fractions in opposite order; this verifies the
statement also for zero rings and empty charts. The case g=id is the same
normalized symmetric product relation. No finite generation, flatness or
nonempty-chart assumption is introduced.

No change record is needed: existing statements, definitions, instances,
attributes, and public imports are unchanged.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.SymmetricProjPullbackGeneratorCrossTensor": "a7ee64cbf335ca916e827ee9f2a8b37bed92cb0c", "Sheaf.AlgebraicGeometry.SymmetricProjPullbackQuotientCrossTensor": "5c6916dcd17d41398cf9c69dc74ada3e062d667a", "Sheaf.AlgebraicGeometry.SymmetricProjQuotientPullbackLocalComparison": "72b7db3806f01f522fda2a863f66ef42be18af2c"}, "results": {"Sheaf.AlgebraicGeometry.SymmetricProjQuotientPullbackComparison": {"hash": "a8d238786c8f78f469222bfa0213c9a000f29de4", "status": "OK"}}, "seconds": 67, "time": "2026-10-28T01:04:48+0800", "transitive": 0, "version": 1}
```

## Second reading by Z6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
