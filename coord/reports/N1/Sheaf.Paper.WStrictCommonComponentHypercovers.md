## What changed

Replaced the sorry in `AlgebraicGeometry.ProEtale.wstrict_common_component_hypercovers`
by a complete Lean assembly of two construction results and a direct proof of the
compatibility over the given scheme morphism. The two construction results are now
separate modules and nodes: a Stonean hypercover of any profinite base, and lifting a
prescribed Stonean hypercover over one w-strictly local affine scheme. Both retain
the original proof plan, source, empty case, and a complete proof in words.

The parent constructs the continuous map with coordinates `(h(v(x)), q(x))`, checks
its component-label equation using `he`, and applies stalk-isomorphism lifting.
It proves the augmentation and coordinate equations. Equality of both coordinates
in the pullback homeomorphism, followed by uniqueness of the scheme lift, proves
naturality for every simplicial operator. This compatibility argument has no hole.

Existing definitions, public imports and theorem signatures are unchanged. No other
existing Lean module is changed. The new statements expand the existing predicates
and component map verbatim, so they can be imported without an import cycle or a
second definition of any notion. The parent node now records the actual assembly.

Validation: all three Lean modules compiled through `lcompile.py --all`; the parent
and the first versions of both new statements took 6--14 seconds each. The final
import cleanup and documentation are also checked by the delivery compilation.

## Proved and sorry left

Closed the original body hole in
`AlgebraicGeometry.ProEtale.wstrict_common_component_hypercovers`
(node `lem-sfb-wstrict-common-component-hypercovers`): 1 of 1 original bodies closed.
There is no sorry in the item module. Its compatibility step is fully proved.

Added exactly two named theorem holes, each with proof exactly `:= by sorry`:

- `AlgebraicGeometry.ProEtale.exists_common_stonean_hypercover`, in
  `Sheaf.Paper.CommonStoneanHypercoverExistence`, node
  `lem-sfb-common-stonean-hypercover-existence`: original steps 1--3.
- `AlgebraicGeometry.ProEtale.exists_common_component_hypercover_single_lift`, in
  `Sheaf.Paper.CommonComponentHypercoverSingleLift`, node
  `lem-sfb-common-component-hypercover-single-lift`: original steps 4--7.

This is a decomposition, not a net reduction of holes: 1 closed, 2 added. The first
remaining result concerns only profinite spaces, with no schemes or comparison map.
The second takes a prescribed hypercover and constructs its lift over just one base;
it contains neither profinite-hypercover existence nor compatibility between bases.
Neither has the hypotheses and conclusion of the parent under another name.

## No longer needed

Removed these proof imports from the item:

- `Sheaf.Topology.StoneanCover`
- `Sheaf.CategoryTheory.SiteFiniteBasisHypercoverExistence`
- `Sheaf.Topology.FilteredSpectrumTopologicalLimit`
- `Sheaf.AlgebraicGeometry.AffineComponentSiteProjection`
- `Sheaf.AlgebraicGeometry.ProEtale.Projective`
- `Mathlib.AlgebraicGeometry.Limits`

The first five still belong to the stated construction subarguments. The finite
spectrum-coproduct result from the last module also belongs to the single-base
construction. Their DAG dependencies are retained in the new nodes. They are no
longer direct dependencies of the parent assembly, and the old direct tool-use
entries are removed from the parent except for stalk-isomorphism lifting. The
original dependency `def-weil-pbc-formal-coproduct` likewise moves to the profinite
construction. The clopen-localization, partition-restriction and incidence-limit
nodes move to the single-base construction. No existing module is withdrawn and
no mathematical construction is claimed globally pruned.

The new statement modules import only what their statements need; their future
proofs will import the proof dependencies recorded in their nodes.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The recorded unit has no realized statement or step
replaced by this decomposition, and the original source route is retained.

The finite-family realization proof must explicitly reindex its finite index types
into the base universe: the generic hypercover theorem allows larger formal-family
index types. This finite reindexing, with operators transported through bijections,
is included in the new profinite node and docstring.

Checked empty bases, empty terms, point bases, `h = id`, and arbitrary `h` satisfying
the component condition. The compatibility proof uses no preservation of closed
points by `h`. All specified ring comparisons and finite-stage normalizations remain
in the single-base statement. The two large unfinished arguments are recorded as
separate tasks, rather than left as internal tactic holes.

## New nodes

`lem-sfb-common-stonean-hypercover-existence`: profinite existence, finite-family
realization in the correct universe, matching surjectivity and augmentation
surjectivity. Source: Stacks 0DAV and 01G2, Bhatt--Scholze Example 2.4.6.

`lem-sfb-common-component-hypercover-single-lift`: the lift over one affine base,
including covers, topology, stalks, components, closed points, weak contractibility
and normalized partition-colimit model. Source: Bhatt--Scholze Lemmas 2.2.8 and
2.4.8, Stacks 097D. Its proof dependencies are the original steps 4--7.

Both nodes inherit the original chapter, unit and blueprint ancestry. Searches by
LeanSearch, LeanFinder and Mathlib grep found generic one-hypercovers, projective
profinite presentations and affine-limit machinery, with no matching all-degree
result. Blueprint searches for Stonean hypercovers, component hypercovers, relative
component lifts and extremally disconnected hypercovers found no duplicate.
No change record is needed: no existing signature or definition changed.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
