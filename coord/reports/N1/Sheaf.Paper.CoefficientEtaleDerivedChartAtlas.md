## What changed

Proved `AlgebraicGeometry.Scheme.coefficient_etale_derived_chart_atlas` with its original
signature unchanged. No existing declaration, definition, public import or module outside
this item was changed.

The proof applies the existing `exists_site_bounded_constant_model` to the fixed-scalar
presentation of K. The existing proved `fixed_lisse` helper supplies its local-cohomology
hypothesis. A private topology/precoverage wrapper keeps every localization at the standard
size. The lower bound is replaced by min(c,d), so reversed bounds are allowed. The covering
is transferred through AsSmall.down; one chart containing each point is selected inside the
existential proof.

Added three modules, all with complete proofs or explicit definitions:

- `Sheaf.CategoryTheory.CoefficientFixedScalarsLocalModels`: standard fixed-scalar derived
  functors and the `CoefficientFixedLocalModel` isomorphism predicate. The scalar equivalence
  reuses the proved theorem in `FiniteComparisonModelRealization`.
- `Sheaf.Paper.CoefficientEtaleChartStalk`: a supplied constant chart identifies its algebraic
  model with any geometric stalk whose point lifts to that chart. Slice restriction preserves
  the pointed filtered colimit. The constant-stalk comparison is proved naturally using
  skyscraper adjunctions, so it applies to all differentials of the model.
- `Sheaf.Paper.CoefficientEtaleChartComparison`: a supplied chart gives the literal-slice
  comparison on any pro-etale object mapping to it. It reuses the proved localized fixed
  pullback square, the constant-ring module equivalence, normalized comparison scalars, and
  `adicExactComparison`. The final isomorphism is lifted through the exact derived scalar
  equivalence on the actual slice.

All additions used by the main proof are private imports. The new public chart lemmas need
no boundedness, finiteness, Noetherianity or covering hypothesis. The stalk lemma only needs
a lift of the geometric point. The comparison lemma only needs the supplied local model and
factorization. No model is chosen as the data of a definition.

## Proved and sorry left

Closed 1 of the item's 1 original holes:
`AlgebraicGeometry.Scheme.coefficient_etale_derived_chart_atlas`
(`lem-sfb-coefficient-etale-derived-chart-atlas`).

Added 0 holes. Every delivered Lean file has zero `sorry` occurrences. In particular,
`coefficient_etale_chart_stalk` and `coefficient_etale_chart_comparison` are proved, not
split-off obligations. This is a proof delivery, not a decomposition.

The original signature was compared verbatim through its conclusion, excluding the proof
assignment, and is unchanged. All four modules compiled together through lcompile.py. One
combined run reported 68 seconds for comparison; its profiling run completed in 25 seconds,
with no long individual proof step. Profiling options were removed before delivery, whose
preflight independently checks the 60-second bound. Empty schemes, empty
charts, zero models and the zero coefficient ring require no separate exception. The bounds
argument also treats c>d.

## No longer needed

No existing public import was removed, and no module is withdrawn. The atlas proof does not
need these old planned dependencies:

- `lem-sfb-constant-scalar-restriction-tensor`, module
  `Sheaf.CategoryTheory.ConstantScalarRestrictionTensor`: tensor or monoidal compatibility is
  unnecessary. The proved ordinary constant-scalar equivalence and exact localization suffice.
- `lem-weil-pbc-constant-sheaf-geometric-stalk`: the new stalk proof computes the natural
  module-valued constant-stalk comparison directly from the skyscraper adjunctions and the
  connected pointed-neighborhood category, rather than using the older additive-sheaf lemma.
- `lem-weil-proetale-weakly-etale-localization`: the conclusion is on the literal slice site,
  so the proof uses the generic slice inverse-image square and never changes to the absolute
  site of the underlying scheme.

The old exact-stalk, fixed-pullback and constant-realization dependencies remain in use
through the new chart lemmas; they are not claimed as pruned. The bounded-model theorem and
geometric-point lift are also retained. No claim is made that the omitted dependencies are
unused elsewhere in the library.

Removed the unused `LocallyConstantFiniteTypeModules` import from the new fixed-scalar
support module after using the existing finite-local-constancy bridge in the main proof.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The planned constant-scalar tensor
package and absolute weakly-etale localization were stronger than this proof needs.
Existing proved private helpers already establish the finite-local-constancy and localized
pullback bridges, and the proved `adicExactComparison` identifies the normalized adic
pullback. Reusing these avoids another split of the same chart-atlas obligation.

The static checker flags the added instance-suppression command and universe w as a
possible interface change. They are documented in
`coord/changes/N1-coefficient-etale-chart-atlas-proof-context.md`; the unchanged direct
importer `Sheaf.Paper.CoefficientConnectedLocalStalkModels` compiled unchanged in 37.5 seconds
against the atlas (44.3 seconds). Its validation copy was removed from the sandbox.
The comparison node's initially truncated `lean.statement` was corrected to include its
letI binder and complete conclusion. LeanSearch was unavailable (one HTTP 502); those
attempts are recorded without a verdict alongside the live alternative searches.

The standard fixed-sheaf derived localizations must be specified explicitly: allowing a
smaller Grothendieck-derived instance would change the literal category in which the chart
isomorphism lives. The private precoverage wrapper and explicit standard slice instances
handle this without modifying a shared definition or disabling respectTransparency.

## New nodes

`def-sfb-coefficient-fixed-derived-models`: the actual exact fixed-scalar functors, standard
slice restriction, and supplied-chart predicate. Its data are explicit existing functors;
its equivalence and exactness proofs reuse proved results.

`lem-sfb-coefficient-etale-chart-stalk`: the supplied-chart stalk calculation, proved.

`lem-sfb-coefficient-etale-chart-comparison`: the supplied-chart literal-slice comparison,
proved. It is strictly independent of covering existence and the stalk calculation.

All three inherit the original chapter, unit and blueprint ancestor. Their Mathlib searches
and exact source places are recorded, and the original node's proof and proof dependencies
now match the Lean argument. Whole-blueprint searches for the chart, constant-stalk and
comparison phrases and source tags found no duplicate blueprint node. The proof-context change record is
`coord/changes/N1-coefficient-etale-chart-atlas-proof-context.md`. No other existing module
or node was adapted.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
