## What changed

Filled the body of
`AlgebraicGeometry.Scheme.finiteEtale_normalTower_commonLevel_cover_gluing`
with a complete Lean deduction from two strictly separate geometric steps. The proof
selects and enumerates an actual finite subcover, forms the product of its levels,
proves positivity, coprimality and all required divisibilities, then combines a coherent
overlap system with its global realization into every field of the original Gluing record.
The original theorem's full signature is unchanged, including the tower assumptions.
The empty subcover is included by the same proof and gives product 1.

Moved the original ten chart/transport definitions and Gluing structure verbatim into
`Sheaf.AlgebraicGeometry.NormalTowerCoverGluingData`, publicly re-exported by the item.
Added Overlaps and Realization records separating, respectively, the existing overlap
fields and global fields. This avoids an import cycle between the two new statement
modules and the original theorem. No definition selects data from an unproved existence
statement, and no definition contains a hole.

The split statements are:

- `normalTower_overlap_system`: only the unique coherent overlap extensions on one
  normal Noetherian level; it asserts no global cover and assumes no covering equation.
- `normalTower_overlap_descent`: effectivity of an explicitly supplied overlap system,
  including the given identification on U. It assumes no normality, generic-point,
  Noetherian or tower hypotheses and must induce that particular system.

Each statement has its own module, complete proof in words, source and DAG node.
The argument follows the original geometric route, with steps 2-3 and 4-6 separated.
Searches found general Mathlib scheme gluing and relative gluing APIs, but no one-line
specialization producing these specified pullback models and compatibility equations.

The existing definitions retain their exact signatures and bodies. The read-only
`tools/downstream.py` search reports zero downstream modules for the item; the direct
import search likewise finds no consumers to adapt. The relocation is recorded in
`coord/changes/S4-normal-tower-cover-gluing-data.md`.

## Proved and sorry left

Original holes: 1. Original theorem bodies filled: 1. Fully discharged original holes:
0; the result is a decomposition into two genuine geometric steps, not a complete
sorry-free proof of the geometry. No sorry remains in the assigned item module.

The original hole reduced is:

- `AlgebraicGeometry.Scheme.finiteEtale_normalTower_commonLevel_cover_gluing`
  (`lem-sfb-normal-tower-common-level-cover-gluing`). Its combining proof is complete.

Holes added and left, exactly two:

- `AlgebraicGeometry.Scheme.normalTower_overlap_system`
  (`lem-sfb-normal-tower-overlap-system`).
- `AlgebraicGeometry.Scheme.normalTower_overlap_descent`
  (`lem-sfb-normal-tower-overlap-descent`).

The data module has zero holes. Thus the textual count changes from one to two holes,
net -1, and this delivery is reported as a decomposition. There are no new axioms or
holes in definitions. The first full compile checked the data module in 8.4 s and both geometric statements in 2.4 s each.
The completed assembly compiled in 2.7 s; final validation also checks the cleaned imports
and retained-hypothesis warning fix. All are below the 60-second file limit.

## No longer needed

Removed the item's proof-only imports:

- `Sheaf.AlgebraicGeometry.RegularNormalDecomposition`;
- `WeilConjectures.AlgebraicGeometry.Morphisms.NormalIntegralGenericHomFull`;
- `Mathlib.AlgebraicGeometry.Gluing`.

Their mathematical roles remain in the two split nodes' proof plans. Those nodes are
not pruned: the overlap proof still needs normal decomposition and generic full
faithfulness, and descent still needs scheme and morphism gluing and Zariski locality.
Base-change stability remains needed as well. No mathematical node, adopted source
module or unit step is withdrawn. The original node's direct proof dependencies now
point to the two split steps, the data node and quasi-compactness. The two existing
tool approvals are retained because their results are still needed in the overlap step.

The shared data module omits the Noetherian, integrally closed ring and sober-space
imports, which only the normality statement needs. They are stated explicitly in that
statement module. The original item's statement imports are retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or false statement was found. The canonical chart comparisons
are already real constructions; they were preserved. The long generic-extension and
scheme-descent steps are not direct specializations of their stated dependencies:
they require component/open restriction transports and a scheme gluing datum with
compatibility equations. The two new statements isolate these separate steps rather
than restating the original tower theorem. Edge cases checked in their proof sketches:
empty index set, empty scheme or overlaps, empty finite etale covers, and an empty
prescribed open (which forces the normal level to be empty when generic containment
is assumed). No nonempty hypotheses were added.

## New nodes

`def-sfb-normal-tower-cover-gluing-data` records the relocated canonical API and the
separation into overlap systems and their global realizations. It has no theorem hole
and introduces no replacement notion of finite etale cover or pullback.

`lem-sfb-normal-tower-overlap-system` is precisely the fixed-level extension, uniqueness
and coherence argument of the original steps 2-3, with no global cover assertion.

`lem-sfb-normal-tower-overlap-descent` is precisely the effectivity argument of original
steps 4-6 for an input coherent overlap system, with all normality assumptions removed
because the isomorphisms are supplied. It preserves the actual transition and
identification equations.

Change record: `coord/changes/S4-normal-tower-cover-gluing-data.md`.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
