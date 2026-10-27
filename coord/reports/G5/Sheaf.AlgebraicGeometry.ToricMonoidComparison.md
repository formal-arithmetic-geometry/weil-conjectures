## What changed

Filled two proof bodies in Sheaf.AlgebraicGeometry.ToricMonoidComparison without changing
any declaration signature, definition, attribute or existing public import. Added private
proof imports of MonoschemeSmoothLocalCharts and ToricRealizationFiniteType.

AlgebraicGeometry.Monoscheme.realizationMap_smooth chooses smallest affine neighborhoods
at source points and their images. The existing restriction theorem supplies the smooth
product charts. The defining realization-map equations identify the composites with the
realized charts; smoothness of open immersions and composition gives smoothness on each
chart. Their jointly surjective open cover gives smoothness globally, without torsion-free
or nonemptiness hypotheses.

AlgebraicGeometry.Monoscheme.isSmooth_of_rational_realization_regular obtains local finite
type from toric_realization_finite_type, transfers perfectness from Q along ULift.ringEquiv,
applies smooth_of_isRegular, and then applies the existing reflection statement. This
closes its own proof body; the reflection theorem remains an explicit dependency.

Updated the parent node proof and proof_deps to record these arguments and the finite-type
dependency. Single-file lcompile passed cleanly in 3.3 seconds, below the 60-second limit.
The arguments retain empty monoschemes and zero-rank charts. No other module is changed.

## Proved and sorry left

Closed 2 of the original 5 holes:

- AlgebraicGeometry.Monoscheme.realizationMap_smooth.
- AlgebraicGeometry.Monoscheme.isSmooth_of_rational_realization_regular.

Three original holes remain, all attached to lem-trf-toric-monoid-comparison:

- AlgebraicGeometry.Monoscheme.toric_ideal_comparison.
- AlgebraicGeometry.Monoscheme.toric_blowup_comparison.
- AlgebraicGeometry.Monoscheme.isSmooth_of_realization_smooth.

Added 0 holes and split off 0 statements. The proved bodies use the existing declared
chart, covering, finite-type and reflection theorems; these dependencies need not yet be
sorry-free in stage 3. This is a partial proof delivery, not completion of all clauses.

## No longer needed

None. No import, node, module or declaration is withdrawn. Existing public imports are
preserved; the three unfinished clauses retain their existing proof plans and dependencies.
Both new private imports are used by the completed proofs. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The ready-item assertion does not match the readable checkout for four recorded proof
dependencies: Sheaf.AlgebraicGeometry.ToricBlowupChartNormalization,
Sheaf.AlgebraicGeometry.SaturatedBlowupProductCharts,
Sheaf.RingTheory.SharpMonoidVertexCotangent and
Sheaf.RingTheory.ToricVertexDimensionFreeness have DAG Lean records but no source file
under their recorded lean/ paths. Searches found neither replacement declarations in
lean/Sheaf or lean/WeilConjectures nor matching rework rows. Their attachments and the
unfinished clauses depending on them are preserved. This delivery does not infer that
these nodes are withdrawn, does not recreate their modules, and does not claim a tool
failure. SmoothToricSaturatedSharpReduction is present but lacks a module header, so it
was not imported or changed. The two completed proofs avoid all these source issues.

The regular-over-Q application also needs the already stated finite-type theorem,
lem-trf-toric-realization-finite-type, rather than only the realization definitions. The
DAG now records this dependency. The two additions are proof-only imports.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
