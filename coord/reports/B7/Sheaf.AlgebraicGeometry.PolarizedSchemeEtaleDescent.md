## What changed

Replaced the hole in `AlgebraicGeometry.exists_polarizedScheme_of_etaleDescent` with a
compiling reduction and an explicit proof of the whole scheme-morphism gluing part.
The private helpers prove the chart maps are over S, their two coordinates are jointly
monic, they form an fppf cover, they detect equality of arbitrary scheme maps, and
compatible realization charts glue uniquely. The proof constructs an overlap test map
explicitly, then constructs the inverse scheme map, checks both inverse identities and
the equation over S, and proves uniqueness of the entire pair isomorphism.

Moved the original sixteen definitions verbatim into
`Sheaf.AlgebraicGeometry.PolarizedSchemeEtaleDescentData` to avoid circular imports.
The item publicly imports this module; its six original public Mathlib/source imports
remain public through the data module. No signature or definition body changed.
Updated the existing definition node's Lean attachment and the theorem node's actual
proof route. Change record: `coord/changes/B7-polarized-descent-data-separation.md`.

The main module compiled in 3.1 seconds; the definition module in 6.6 seconds and each
new statement module in about 3 seconds, using only lcompile.py. The sole direct
consumer, `PolarizedFineLogEtaleDescent`, compiled individually against the extraction in 3.9 seconds.
No consumer adaptation is needed. The report records a decomposition, not a completed
axiom-free proof of effective polarized descent.

## Proved and sorry left

Original holes: 1. Its theorem body is now complete Lean:
`AlgebraicGeometry.exists_polarizedScheme_of_etaleDescent`
(`lem-trf-polarized-scheme-etale-descent`). This is a decomposition, not a net hole closure.

Three holes added, each the whole proof of a named public theorem in its own module:

- `AlgebraicGeometry.exists_polarizedSchemeCharts`
  (`lem-trf-polarized-scheme-charts`): only the underlying scheme and theta charts;
  no global ordinary module or line comparisons are concluded.
- `AlgebraicGeometry.exists_polarizedModule_on_schemeCharts`
  (`lem-trf-polarized-module-on-charts`): module effectivity on an already fixed scheme
  with already supplied scheme charts and their transition equation.
- `AlgebraicGeometry.existsUnique_polarizedLineIso`
  (`lem-trf-polarized-line-iso-descent`): module full faithfulness over an already
  supplied chart-compatible global scheme isomorphism, with no scheme gluing assertion.

The item module and extracted definition module have zero sorries. Net holes: 1 removed
and 3 added, hence -2 net closed. Each remaining statement has its source, full proof in
words and matching node; none is the original conclusion with repackaged hypotheses.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.AlgebraicSpace`
- `WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf`
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAmpleLocal`
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceInvertibleDescent`
- `Sheaf.AlgebraicGeometry.EtaleRelationQuotient`

The algebraic-space, relation, quotient-chart, invertible-descent and relative-ampleness
nodes remain needed by `lem-trf-polarized-scheme-charts`; they are not claimed as pruned.
`lem-trf-etale-scheme-line-morphism-gluing` is no longer used by this proof route:
the scheme portion is proved here directly from subcanonical sheaf gluing, while the
remaining module portion is isolated over a fixed scheme isomorphism and cites the
more basic fpqc module full-faithfulness statement. The small-etale representable
sheaf import is unnecessary: big fppf subcanonicity handles all target schemes directly.
No existing module or DAG node is withdrawn. Module pruning claimed: none. The obsolete top-level `tool_uses` approval for
`lem-weil-pbc-small-etale-representable-presheaf-sheaf` is removed from the item node.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed or weakened. The planned relation-construction lemma uses
an index in the scheme universe, but this item's index universe is independent.
The remaining scheme-chart lemma explicitly accounts for a small jointly surjective
subfamily chosen by points of S, and recovery of every original chart by descent.
The quotient theorem takes its sheafification and its universal property as inputs;
constructing that quotient, rather than assuming arbitrary big-site sheafification,
remains part of the scheme-chart obligation. Its proof plan retains the original
quotient/algebraic-space/ample route.

The existing ordinary-module descent and pair-morphism interfaces do not immediately
supply this item's pinned tensor comparisons. The two module obligations isolate that
normalization, with the existing `lem-pc-fpqc-descent` and tensor-composition associativity
as generic tools. These are module-descent tools, not a replacement of any unit route.
No changes to a unit, chapter, adopted source module, target or another worker's module.

Checked edge cases in the new statements: empty S and empty index family, repeated
cover members, an index larger than the scheme universe, arbitrary non-affine bases,
and non-quasi-compact etale cover arrows. No new statement adds quasi-compactness,
separatedness, finite type, nonemptiness or a fixed finite covering to the original data.
The scheme gluing proof works on every test scheme, not only its points.

## New nodes

`lem-trf-polarized-scheme-charts`, module `Sheaf.AlgebraicGeometry.PolarizedSchemeCharts`:
the original quotient, line descent and relative-ampleness steps give only the scheme
with its theta charts. The module effectivity and uniqueness conclusions stay separate.

`lem-trf-polarized-module-on-charts`, module
`Sheaf.AlgebraicGeometry.PolarizedModuleOnCharts`: ordinary invertible-module effectivity
on a fixed scheme, including the exact lambda normalization.

`lem-trf-polarized-line-iso-descent`, module
`Sheaf.AlgebraicGeometry.PolarizedLineIsoDescent`: unique compatible module isomorphism
over a fixed global scheme isomorphism. All scheme-map descent is proved in the item.

The nodes share the original chapter, unit and blueprint ancestry. Logged LeanSearch,
LeanFinder/Loogle and Mathlib grep searches are recorded honestly. Searches found generic
scheme/prestack gluing but no exact polarized tensor-comparison bridges. Existing source
fpqc module descent is retained as a tool, not duplicated as a new general descent theorem.

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
