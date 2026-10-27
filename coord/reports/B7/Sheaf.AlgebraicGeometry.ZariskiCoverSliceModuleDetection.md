## What changed

Proved both theorems in `Sheaf.AlgebraicGeometry.ZariskiCoverSliceModuleDetection`,
without changing either signature or any public import. Added proved private helpers for
sectionwise zero objects, covering restriction injectivity, zero detection by slice
restrictions, empty-site vanishing, and the two covering criteria. The only library
interface used beyond Mathlib is the existing `ringedSiteModules` abbreviation.

The proof checks open-cover membership directly using
`ofArrows_mem_smallEtaleTopology_iff`; the pro-etale precoverage proof uses
`etalePrecoverage_le_proetalePrecoverage` after forgetting to schemes, retaining its full
quasi-compact refinement requirement. Slice covers use `mem_over_iff` and
`Sieve.overEquiv_ofArrows`. Module separatedness proves injectivity and zero detection;
restriction evaluates sectionwise by reflexivity. The empty etale covering is explicitly
indexed by `PEmpty.{1}`, and `ProEt.bot_mem_topology` gives the empty pro-etale cover.

Read Stacks 098B, 00VM (including the empty-cover remark), 00Y0, 04IX(4), and 03CW in the
local sources. Checked the current smooth-purity unit; no unit statement or route changes.
Updated the item's proof steps and dependencies to match this direct implementation.
All work is confined to the assigned sandbox.

## Proved and sorry left

Closed both original holes:

- `AlgebraicGeometry.Scheme.zariskiCoverEtaleModuleDetection`.
- `AlgebraicGeometry.Scheme.zariskiCoverProetaleModuleDetection`.

Both realize `lem-pur-zariski-cover-slice-module-detection`.
Holes closed: 2. Holes added: 0. Holes remaining in the delivered module: 0.
No split-off statements or new axioms. The proof handles empty schemes, empty indexing
families, repeated/empty opens, arbitrary infinite indexing families and arbitrary ring
sheaves without extra assumptions; these cases are covered by the unchanged signatures
and the generic separatedness argument.

## No longer needed

Removed the private imports `Sheaf.CategoryTheory.SiteCoveringAxioms`,
`Mathlib.AlgebraicGeometry.OpenImmersion` and
`Mathlib.AlgebraicGeometry.Morphisms.Etale`. The latter two are already available through
the retained public Mathlib site imports; their mathematical open-immersion/etale facts
remain used. No public import was changed.

The proof does not need `def-weil-pbc-sites-and-cohomology`'s extra
`Precoverage.IsSiteForCoverings` interface (module
`Sheaf.CategoryTheory.SiteCoveringAxioms`), nor the standalone
`lem-weil-pbc-open-immersion-base-change` dependency: inverse-image open families are
verified directly by the small-site covering criteria. Both are removed from the node's
proof dependencies. The Mathlib Grothendieck-topology pullback axiom is still used for
sieve-based local zero detection. No other node or module is withdrawn; other consumers
of these dependencies are unaffected.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was false. The planned chosen-pullback/base-change step was
unnecessary because the theorem already names inverse-image open subschemes explicitly.
For local zero detection, pulling back the covering sieve gives the requisite maps to
cover members directly and avoids additional scheme factorization constructions.
The standalone site-axioms declaration is a predicate, not a supplied proof of the site
axioms; the existing Mathlib Grothendieck topologies already supply the axiom needed here.

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
