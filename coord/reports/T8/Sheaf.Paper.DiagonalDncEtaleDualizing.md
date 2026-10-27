## What changed

Replaced the hole in `diagonalDncEtaleNaturality_dncDualizing` by composition of
an inverse-deformation square and a source-to-dualizing square. The statement,
all binders, and both existing public imports stay unchanged. The two new proof
imports are private.

`DiagonalEtaleSourceTransport` constructs the missing intermediate source comparison.
The construction factors the actual self-product map through a Cartesian pullback,
uses the specified counit-normalized etale locality and inverse smooth section base
change, and transports by the canonical site comparisons. The etaleness and section
equation of the intermediate map are proved. The common-source transport contains
neither delta nor the normal transport. The separate `sourceToDualizing` is precisely
alpha, inverse rho, and coefficient-unit change. These are actual constructions;
no existence witness, DNC comparison, or desired naturality equation defines them.

The original proof now expands the four factors, uses `Functor.map_comp`, rewrites
with the inverse-deformation square, and then rewrites with the independent
source-to-dualizing square. This is a decomposition, not a net closure of the
underlying geometric compatibility.

## Proved and sorry left

Original holes: 1.

Closed in the assigned module:
`WeilConjectures.PurityFiniteSetting.diagonalDncEtaleNaturality_dncDualizing`
(node `lem-pur-diagonal-etale-dnc-dualizing-square`), conditionally on the two
separate factor squares below.

Added holes: 2, both whole named public theorem proofs:

- `WeilConjectures.PurityFiniteSetting.diagonalEtaleInverseDeformation`
  (`lem-pur-diagonal-etale-inverse-deformation-square`), comparing inverse delta
  with the source and actual Rees-normal transports. It contains no alpha, rho,
  unitChange, ordinary dualizing locality, beta, or integration. It also removes
  the original compactification and Noetherian hypotheses unnecessary for this factor.
- `WeilConjectures.PurityFiniteSetting.diagonalEtaleSourceDualizing`
  (`lem-pur-diagonal-etale-source-dualizing-square`), comparing alpha, inverse rho,
  and unitChange with source locality. It contains no delta, normal invariant,
  normal transport, beta, or integration.

Proved with no new holes: `DiagonalEtaleComparison.sourceLift_geometry` and every
construction in `DiagonalEtaleSourceTransport`. The two new equations are disjoint
parts of the original map; neither asserts the original conclusion under another
name or assumes the original square. The main proof performs their actual pasting.
Holes remaining in the assigned module: 0. Holes in the delivered modules: 2.
Net holes closed minus added: -1; report as decomposition.

## No longer needed

No original import is removed, and no module is withdrawn or globally pruned.
The old direct proof dependencies are now used by the two factor obligations,
not directly by the assembling theorem; the item's proof dependency list now names
only these two obligations. In particular section-etale coherence, DNC invariance,
diagonal base change and the counit comparison data are still needed transitively.
No unit statement or step is bypassed.

`GeneralChartComparisons` and its `ChartDncSquare`/`ChartDiagonalSourceSquare` interface
cannot be imported: `import_direction.py may` reports that `GeneralChartComparisons`
already reaches the assigned item. Moreover its chart hypotheses require a global
etale coordinate chart, which the assigned arbitrary smooth maps do not have.
The new source construction uses the lower-level normalized locality and smooth
section exchange already available here, analogous to the existing orientation-free
`DiagonalEtaleSectionComparisons`. The downstream chart orientation, beta and
vector-integration results are not used by this proof.

## Where the brief, the DAG or earlier work was wrong

The old node correctly describes the two geometric factors but does not expose their
source-section interface. Its declared section-coherence theorem concerns Cartesian
maps of section pairs, whereas the self-product of an etale map has extra clopen
components over the diagonal. Identifying the actual source/normal composites after
cutting those components, and identifying the ordinary dualizing locality for every
normalized N, are substantive compatibility equations. They are now separated at
the actual source invariant, with their source and full argument recorded in the
new docstrings and nodes.

The existing general chart definitions could not supply this interface by import
because that would create a cycle. They have not been edited. The existing ancestry
helper prints `blueprint.from.node = None` for this item's created-for module name;
the actual parent nodes identify `thm-pur-diagonal-dualizing-object` as the blueprint
ancestor, and the new nodes record that source directly. The item and unit metadata
outside the allowed proof fields are preserved.

Edge cases checked: O empty, rank d=0, identity etale maps, f=g, and identical lifts.
The transport always uses the same common smooth source, the two induced Rees maps,
and the same normalized counit mates; no absolute separatedness of aY, nonempty
open, or coefficient orientation is introduced.

Validation: `lcompile.py --all` compiled all four delivered modules successfully.
The original theorem signature was checked against the shared source and is unchanged.
The line-length warning in the compiled snapshot has been corrected in the final source.

## New nodes

`def-pur-diagonal-etale-source-transport` records the explicit source-section
transport and the pre-deformation source-to-dualizing factor. Its Lean module is
`Sheaf.Paper.DiagonalEtaleSourceTransport`; it has no holes.

`lem-pur-diagonal-etale-inverse-deformation-square` records just the DNC endpoint
square, in `Sheaf.Paper.DiagonalEtaleInverseDeformation`.

`lem-pur-diagonal-etale-source-dualizing-square` records just alpha/rho/unitChange
naturality, in `Sheaf.Paper.DiagonalEtaleSourceDualizing`.

Mathlib searches were run using msearch: LeanFinder, LeanSearch, Loogle and grep.
They found generic etale/base-change facts and `Functor.map_comp`, not either
compatibility equation. Blueprint searches for deformation/etale and diagonal/source
returned no matching imported blueprint statement. No existing shared module or
another module's node is changed; no change record is required.

## Second reading by T8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
