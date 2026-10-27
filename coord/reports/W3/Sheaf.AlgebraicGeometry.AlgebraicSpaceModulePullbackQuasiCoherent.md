## What changed

Replaced the item theorem's `sorry` with a complete Lean proof constructing
`SheafOfModules.QuasicoherentData`. Choose the given local presentations, use
all commuting scheme-chart triangles over their covering charts, map each
presentation with Mathlib `Presentation.map`, and transport it with
`Presentation.ofIsIso`. A local left adjoint preserves the coproducts and
cokernels used by arbitrary presentations. No flatness or finiteness assumption
was added, and the original theorem signature is unchanged.

The two geometric interfaces not directly supplied by the existing declarations
are stated separately: pulling back the covering and refining by scheme atlases;
and the natural chart-local tensor-pullback comparison, including its
structure-module isomorphism and the slice sheafification prerequisites. Both
are strict parts of the original proof, independent of quasi-coherence of a
module. The latter concerns every module and one chart triangle; the former
concerns only the underlying sites. Neither restates the item theorem.

All three modules compiled in the remote sandbox: 2.5 seconds for the covering
lemma, 2.6 seconds for the chart comparison, and 2.7 seconds for the item.
The only subsequent change before delivery was source/docstring formatting.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.AlgebraicSpace.isQuasicoherent_moduleTensorPullback`.
Its combining proof is complete.

Added two named subsidiary holes:

- `AlgebraicGeometry.AlgebraicSpace.moduleChart_coversTop`, in
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleChartCover`.
- `AlgebraicGeometry.AlgebraicSpace.moduleTensorPullback_chart_functor`, in
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleChartPullback`.

The item now has zero holes; the delivered three modules have two holes total.
This is a decomposition (one hole closed, two added), not a net proof gain.
Each remaining hole has a source, a complete proof in words, and a new DAG node.
There are no new definitions, axioms, or arbitrary data constructions from an
unproved existence theorem. Local functor witnesses are eliminated only inside
the proposition proving quasi-coherence.

## No longer needed

Removed these proof-only imports from the item:

- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.PullbackLocalizationOfUniverses`
- `Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence`

The item directly needs only the two new interfaces, the quasi-coherence data
API, and left-adjoint colimit preservation. Its original proof dependencies for
enlarged ringed sites, enlarged chart ringed morphisms, chart-limit/enlarged
sections, the module adjunction, localized pullback, and chartwise permanence
remain needed in the proof plans of the new lemmas. The tensor-product node is
likewise still needed there. They are not claimed as globally pruned. The
original public imports are preserved. No existing declaration, module, or unit
route is withdrawn, and no whole mathematical dependency is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

No disputed statement or false source claim was found. The original proof plan
was mathematically appropriate, but its declarations do not directly expose the
small-site chart covering or the chart-local functor triangle in the required
universes. These are now explicit intermediate obligations rather than implicit
glue. The existing small-site slice file publicly supplies weak sheafification,
while Mathlib `Presentation.map` requires full left exact `HasSheafify` on the
two slices. Its internal proof already constructs that stronger fact using the
scheme slice equivalence and the small affine etale basis. The local comparison
lemma includes exactly these two stronger prerequisites, without changing the
existing slice module's interface.

The covering statement was checked on empty families and empty spaces. A map
to an empty target has empty source, so the empty-family case is consistent.
The comparison is required for all commuting chart triangles, not just covering
charts, and for all modules. Its proof uses ringed-site localization and the
normalization of the actual chart-limit direct image, so it does not silently
replace `moduleTensorPullback`. Non-flat morphisms and infinite presentations
require right exactness and colimits, not exactness or finite free modules.

## New nodes

- `lem-sfb-space-module-chart-cover`: scheme charts over the pulled-back
  covering cover the source. Source: Stacks 03DO, 03G2 and 03DN.
- `lem-sfb-space-module-chart-pullback`: the localized left adjoint, its unit
  comparison, natural compatibility with the actual global pullback, and slice
  sheafification. Source: Stacks 04J0, 04J1, 03D7, 03DF and 03G8.

Both are new one-statement modules in the item's chapter and unit. Their nodes
record the actual signatures, source proofs, Mathlib searches, and existing
prerequisites. The item's node now records the complete assembly proof and the
two new dependencies. The inherited blueprint route and all target statements
are preserved.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
