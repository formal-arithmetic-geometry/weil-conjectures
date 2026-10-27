## What changed

In `lean/Sheaf/AlgebraicGeometry/SpaceChartLimitEnlargedSections.lean`, filled the
linearity and chart-projection naturality proofs. All existing declaration signatures
and definitions are preserved.

`enlargedModuleChartRestriction_linear` composes the additive extended-module
restriction with the extension counit. For scalar compatibility it evaluates
`enlargedStructuralMap_existsUnique`'s normalization at the scalar, cancels the
structure restriction isomorphism, and applies semilinearity of the extended module
and linearity of the counit.

`enlargedModuleChartProjection_naturality` proves the equality of the actual arrows
into the fibre product using its two projections and the chart triangle equation.
Naturality of the extension counit and the extended module's composition law then
identify the section maps. A local heartbeat allowance covers the nested module
restriction elaboration; the compile still meets the 60-second wall-time limit.

This realizes the linearity and cone portion of Step 2 of
`lem-trf-space-chart-limit-enlarged-sections`, using its stated enlarged-site
structural normalization. It makes no change to the planned remaining route or
unit. No DAG changes or definition/interface change records are required.

Read Stacks `spaces-properties.tex`, `lemma-morphism-ringed-topoi` (03G8) and
`remark-explain-equivalence` (03H7), and `spaces-morphisms.tex`,
`lemma-compute-pushforward` (03M8). Searches via LeanFinder, Loogle, the search
wrapper's grep, and local searches in Mathlib and both library roots found no direct
replacement for the all-chart comparison. Loogle identified
`PresheafOfModules.map_smul`; the proof uses that API together with
`PresheafOfModules.naturality_apply`, `map_comp_apply`, and `congr_map_apply`.

Validation: the module compiled on the project server with `lcompile.py` in 26.7 seconds.
The final simplifier suggestion was replaced by its explicit `simp only` proof;
`deliver3.py` performs the final compile and preflight.

## Proved and sorry left

Closed 2 of the original 4 holes, with no holes added or split off:

- `AlgebraicGeometry.AlgebraicSpace.enlargedModuleChartRestriction_linear`.
- `AlgebraicGeometry.AlgebraicSpace.enlargedModuleChartProjection_naturality`.

The two original holes left, with their original statements and complete proof plans:

- `AlgebraicGeometry.AlgebraicSpace.space_chart_limit_enlarged_sections`
  (`lem-trf-space-chart-limit-enlarged-sections`, Steps 1 and 3–7).
- `AlgebraicGeometry.AlgebraicSpace.space_chart_limit_enlarged_localization`
  (`lem-trf-space-chart-limit-enlarged-sections`, Steps 8–9).

The proofs use the existing normalized extension equivalence and structural-map
normalization declarations; their upstream proof obligations remain with their
own modules. This is a partial proof delivery, with a net reduction of two holes.

## No longer needed

Removed the unused private imports
`Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence` and
`Sheaf.CategoryTheory.RingedToposMorphism`. Neither completed proof invokes those
modules' declarations. The remaining public imports are needed by existing
statements and definitions.

The completed proofs do not need an atlas, descent equalizer, chartwise permanence,
localization, or a ringed-topos comparison. Those belong to the two remaining
obligations, so no node, module, or dependency in their unresolved plans is
withdrawn. No source-library declarations are removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found in the completed clauses. The structural map's
normalization is already supplied by `enlargedStructuralMap_existsUnique`, so the
cone's linearity does not require an additional ringed-topos comparison theorem.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
