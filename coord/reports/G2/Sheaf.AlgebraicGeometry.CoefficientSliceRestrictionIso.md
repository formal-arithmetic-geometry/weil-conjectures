## What changed

Proved `AlgebraicGeometry.ProEtale.IntegralModelsStacks.coefficient_slice_iso_of_internal_restriction_iso` with its signature unchanged. The proof constructs the actual internal/fixed-scalar inverse-image comparison by taking the adjunction mate of an identity-on-sections direct-image comparison. It then transports the input isomorphism using the internal pullback compositor and weakly etale localization of the slice.

Added `Sheaf.AlgebraicGeometry.ConstantCoefficientChartPullback`, containing the proved ring-only theorem `exists_constant_coefficient_chart_pullback`. It transports the constant chart and proves compatibility with the concrete coefficient map on constant scalars. Its reconstruction step uses the existing proved general private helper `reconstructedCoefficientPullback` through a proof-only `import all Sheaf.Paper.IntegralSectionCoefficientNaturality`; that helper works for arbitrary condensed coefficients, without the integral specialization of that module's public theorem. The constant-ring comparison is proved using constant-sheaf adjunctions and their units. All helper definitions contain actual constructions and all private helpers are proved. The mate construction and final isomorphism composition are factored over arbitrary categories. A private site equivalence, generic in its value category, is compiled once in the new ring module and reused by the item via a proof-only import all. The comparison with the displayed literal model uses the functor associator, transported through pullback and slice restriction, avoiding repeated reduction of reconstructed module actions. All irreducibility attributes used for this purpose are local to the item. The input point-restriction conversion is made for an arbitrary structural scheme map before its site-object specialization; this avoids expanding the typed point model during the final kernel check. The first clean delivery compile passed in 50.8 seconds for the item and 34.7 seconds for the ring helper; its two letI style warnings were corrected. Delivery runs the final checks.

Updated the item's proof steps, proof dependencies, and proof origin. Both existing public imports stay unchanged; added imports are proof-only. No other existing Lean module or node is changed.

## Proved and sorry left

Closed 1 of 1 original holes: `AlgebraicGeometry.ProEtale.IntegralModelsStacks.coefficient_slice_iso_of_internal_restriction_iso` (`lem-sfb-coefficient-slice-restriction-iso`).

Added 0 holes. The new `AlgebraicGeometry.ProEtale.IntegralModelsStacks.exists_constant_coefficient_chart_pullback` (`lem-sfb-constant-coefficient-chart-pullback`) is proved. No `sorry` remains in either delivered module; no obligation is split off.

## No longer needed

No existing imports were removed, and no modules are withdrawn. This proof does not use the planned `lem-c2-proetale-section-module-algebraic-inverse-image` (`Sheaf.Paper.SectionModuleAlgebraicInverseImage`) or `lem-sfb-internal-module-inverse-image-comparison` (`Sheaf.CategoryTheory.InternalModuleInverseImageComparison`): the needed comparison follows directly from the already proved `InternalModuleOperations.lowerComparison` and adjunction mates. These two planned edges are removed from this node's proof dependencies.

The direct proof edge to `lem-cbc-constant-ring-module-sheaves` is also unnecessary: the proved `coefficientModelFixedScalars_isEquivalence` from `FiniteComparisonModelRealization` provides the equivalence needed here. This is not a claim that its transitive dependencies, or any upstream declarations, can be removed. The integral-model unit's route is preserved.

## Where the brief, the DAG or earlier work was wrong

No statement repair was needed. The planned intermediate inverse-image comparisons are more general than necessary. Comparing the concrete right adjoints first avoids reopening them and keeps the scalar compatibility check sectionwise.

The generic reconstructed coefficient-ring pullback comparison was already fully proved inside `IntegralSectionCoefficientNaturality`, although its public theorem is specialized to integral coefficients. Reusing that generic helper avoids another split of the module comparison. It is a generic ring-theoretic tool, not a replacement of the integral-model unit's argument. The constant-sheaf unit check and the slice functor check work for empty schemes and for the zero ring as well.

## New nodes

`lem-sfb-constant-coefficient-chart-pullback`: a proved coefficient-ring transport lemma, strictly smaller than the module/slice theorem. Its statement has no input module or slice. Its proof composes the existing reconstructed ring pullback isomorphism with the inverse-image comparison for constant ring sheaves, then verifies the scalar unit equation and transports by AsSmall. The node records Mathlib searches and its blueprint provenance. There are no change records because no shared statement or definition was changed.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
