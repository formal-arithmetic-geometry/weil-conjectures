## What changed

`ProjectiveLineDiagonalIntegrals` now constructs the Cartier witness from the proved
smooth-diagonal regular-immersion theorem, obtains the normalized supported class from
`ordinary_supported_kummer_uniqueBoundary`, and proves both integration equations from
the pre-trace two-component Chern calculation. The constant-unit component has trace
zero by the biproduct decomposition; the relative Chern component has trace identity.
The original projection, chart and alpha constructions remain in their original module.
The trace factors its four chart comparisons through the explicit
`ordinaryFiniteShiftedLineChart`; all factors and their order are preserved.
The theorem's hypotheses, supported boundary, exact realization and conclusion are unchanged.

`OrdinarySupportedChernNormalization` proves
`ordinary_supported_kummer_chern`: uniqueness identifies any normalized supported
representative with the supported theorem's witness; its unit and scalar-Chern
clauses then compute the ordinary cohomology class. This theorem is proved completely.

`ProjectiveLineDiagonalChernAdjunct` is a new module for the independent global
O(1,1) class calculation, before any trace. It also gives the concrete chart comparison.
The Chern calculation concerns an ordinary Chern arrow, with no supported representative,
and works over any base and specifies both components, whereas the
item only asks for the integral over a Noetherian base. It is a strict geometric part
of the argument, not a renamed integration equation. The upper proof additionally
constructs the Cartier and supported witnesses and proves the biproduct trace calculation.

## Proved and sorry left

Closed in the item: `AlgebraicGeometry.Etale.projectiveLine_diagonal_integrals`
(node `lem-amb-p1-diagonal-integrals`): one of its one original holes.
The private Cartier argument, `ordinary_supported_kummer_chern`, and all
trace-combination steps contain no `sorry`.
The item contains zero remaining holes.

Added: `AlgebraicGeometry.Etale.projectiveLine_diagonal_chern_adjunct`
(node `lem-amb-p1-diagonal-chern-adjunct`): one named theorem with one `sorry`.
The new normalization module has zero holes.
This is a decomposition: one upper hole closed and one lower hole added, net zero
among these declarations. Imported pre-existing holed theorems are not claimed as proved.
No definition contains a hole and no arbitrary witness is chosen to define data.

## No longer needed

Removed direct proof imports:

- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.AlgebraicGeometry.GeometricFiberFinite`
- `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`
- `WeilConjectures.AlgebraicGeometry.EffectiveCartier`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits`
- `Mathlib.CategoryTheory.Adjunction.Basic`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction`
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`
- `Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`
- `Mathlib.AlgebraicGeometry.Pullbacks`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts`
- `WeilConjectures.SixFunctors.Finite.Exact`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `Mathlib.CategoryTheory.Sites.Point.Basic`
- `Mathlib.CategoryTheory.Sites.Point.Skyscraper`
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact`

The global class calculation replaces the geometric-fibre exchange and stalk-detection
route. The item no longer directly uses nodes `cor-weil-pbc-geometric-fiber-finite`,
`prop-weil-pbc-geometric-stalks-exact`, or
`lemma-weil-pbc-geometric-stalk-conservative`; their top-level tool approvals are removed.
The module also no longer directly requires the separate ordinary adjunction-existence
proof: it uses the trace datum's specified biproduct decomposition and Chern normalization.
The supported-class theorem and trace still have their own dependencies; no assertion
is made that a removed direct import is globally unreachable. Standard charts and
transition calculations remain needed by the new geometric node. No library declaration,
module, or existing DAG node is withdrawn.

The previous attempt's unlanded `ProjectiveLineDiagonalIntegralReduction` and
`ProjectiveLineDiagonalFoundations` modules are not needed: the actual proof and original
constructions reside in the item. Their scratch copies are retained outside the packet.

## Where the brief, the DAG or earlier work was wrong

The prior sandbox report claimed that the item was proved while its source still had
`sorry`. This packet replaces that claim with an actual Lean proof and accounts for
its remaining geometric hole explicitly. The earlier 60-second compiler stop was not
a tool failure. Profiling showed costly normalization around generic derived functors
and the large simultaneous supported-witness theorem. The proof uses the already-proved
existence-and-uniqueness boundary theorem to avoid extracting the unused full witness
system. An attempted specialized-map wrapper did not improve normalization and is omitted.
The resulting files compile within the unchanged 60-second limit: 39.8 seconds for
the normalization module, 23.7 seconds for the class module, and 51.8 seconds for
the item in the all-files check. Its one reported long-docstring line has been wrapped.

Consumer inspection found `FiniteP1ArbitraryBaseIntegrals` (G5) and
`ProEtaleProjectiveLineTrace` (unclaimed). Both use the unchanged projection/chart
interfaces and neither mentions `projectiveLineDiagonalTrace`; no adaptation is needed.

The generic scalar-realization injectivity needed by the new geometric node already
exists as `kummerFirstChernRealization_bijective` in `Sheaf.Paper.KummerAdditivity`;
its node is cited rather than splitting off a duplicate. The actual ordinary divisor
line isomorphism and its compatibility with the canonical chart adjunct remain the
open geometric work. `ProjectiveSpace.pullbackMapTwistIso`,
`Scheme.gmCohomologyMap_toCohomologicalPicardGroup`, and
`Scheme.rootsOfUnityCohomologyMap_kummerδ₁` provide the existing base-change tools.
Scratch proofs compiled both scalar Chern additivity (Picard multiplication followed
by two additive maps) and canonical Chern uniqueness (the bijective realization and
`Equiv.eq_symm_apply`), as well as Kummer/Picard pullback naturality. These establish
the exact generic interfaces for the remaining proof; they do not assert the missing
diagonal line identification. The Segre bilinear-chart transition theorem supplies
product-chart transition units but does not identify the diagonal ideal with their line.

The DAG originally planned a fibre-by-fibre calculation. The new node records a global
refinement of the same determinant/O(1) calculation, giving both components before trace.
The unit route is preserved. Edge cases checked in the new proof description include
empty and nonreduced bases, arbitrary finite coefficient rings, and N=1 (zero twists).
No target statement or adopted source-library declaration is changed.

## New nodes

`lem-asd-ordinary-supported-chern-normalization`: a fully proved projection of the
supported Kummer theorem, computing the actual ordinary scalar cohomology realization
of any uniquely normalized supported class. It introduces no new assumption or hole.

`lem-amb-p1-diagonal-chern-adjunct`: the diagonal divisor has line O(1,1), hence its
normalized Kummer class has the base-Chern and relative-Chern components in either
canonical projective-line chart. Its module has one theorem hole with a complete
proof in words and uses no trace. Its DAG record gives the geometry, Kummer additivity,
scalar realization, and adjunct steps with their existing dependencies.

Change record: `coord/changes/A7-projective-line-diagonal-trace-factor.md`.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
