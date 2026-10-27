## What changed

Replaced the proof of `AlgebraicGeometry.immersiveSystem_source_local_fractions` in
`Sheaf.AlgebraicGeometry.ImmersiveSystemSourceLocalFractions`. The statement and public
imports are unchanged. Added private proved helpers for polynomial evaluation onto a
projective chart, fractions in the stalk of an immersion into an affine chart, and the
local-fraction result on the source of a generating-section morphism. The final proof
transports this result along the open-inclusion stalk isomorphism, preserving the chosen
tensor-pullback unit and the original coefficient germs.

Proof imports added: `Sheaf.AlgebraicGeometry.CompleteLinearSystemClosed` (only
`generatingSections_pair` is used),
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ChartSections`, and
`WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator`.
The existing node's proof, proof dependencies and proof origin follow this argument.
No definitions, public signatures, source-library declarations or other modules changed.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.immersiveSystem_source_local_fractions`
(node `lem-zl-immersive-system-source-local-fractions`).
No holes added, no split-off statements, and no `sorry` remains in the delivered module.
Validation: `lcompile.py` compiled the complete module cleanly in 9.7 seconds.
All three added proof imports pass `tools/import_direction.py may`. The theorem
signature and all public imports were compared verbatim with the original; all Lean
lines are at most 100 characters. The delivery preflight supplies the axiom check.

## No longer needed

The proof does not use `lem-weil-pbc-invertible-generating-sections-fibre` or
`Sheaf.AlgebraicGeometry.ProjectiveMorphismChartPreimage`
(`lem-weil-pbc-projective-morphism-chart-preimage`). Both dependencies are removed from
this node's proof route: the projective chart cover chooses the denominator coordinate,
and the existing section-preserving pair gives the free-generator and ratio statements
directly. No global withdrawal of these modules is claimed; other consumers may need them.

The proof also avoids importing
`Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts`: the adopted source's proved
`iSup_standardOpen`, `isAffineOpen_standardOpen`, and
`closure_range_appLE_union_range_coordRatio` suffice. The standard-chart node remains a
mathematical proof dependency. No existing import was removed and no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The DAG's separate fibre-nonvanishing argument and its
conversion r=n+1 are unnecessary. Choosing a chart containing the image point works for
all finite coordinate types; with an empty coordinate set the chart-cover membership
immediately supplies the contradiction. The original local-ring argument is otherwise
followed, including its specified scalar map and arbitrary local frame. No unit route is
bypassed.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
