## What changed

The original statement and every public definition of
`Sheaf.Paper.TraceBoundedQuotientStalkRealization` are preserved. Its proof now
combines the finite germ-tower comparison, exact pullback compatibility with good
truncations, and the uniform quotient cohomological interval. Proved private
helpers construct the bounded zigzag, preserve its arrows through the stalk and
Roos functors, identify the prescribed scalar Roos map with the existing natural
Roos isomorphism, and derive the required representative naturality equation.

The realization isomorphism is built factor by factor from the published
pullback comparison, derived sections factorization, sectionwise Roos comparison,
and germ tower isomorphism. Its hom is definitionally the prescribed original
arrow. A composite natural transformation is used only in the naturality
argument. The proof supplies a private local witness for module limits of the
required size, avoiding an ambiguous universe maximum during inference. The new
proof section restores transparency checks and uses a proved Roos functor-map
equation to avoid unfolding the cone construction.

Three new modules and their nodes isolate the cohomological-bound argument and
the two remaining independent comparisons. No existing signature, definition,
public import, or consumer is changed; no change record is required.

Validation: server `lcompile.py --all` accepts all four modules within the
per-file compile limit. The profiling options used to locate repeated map
expansions are removed from the delivery. The final naturality argument keeps
the scalar Roos and germ maps together under localization, as in the prescribed
arrow, and uses a proved generic three-factor naturality calculation.

## Proved and sorry left

The original module had one hole, `WeilConjectures.trfBoundedQuotientStalkRealization`.
That proof is replaced by a complete combination of named results, with no hole
in the module. `WeilConjectures.integralQuotientCohomologicalBounds` is proved
from the existing derived reduction counit and exact restriction of scalars.

Two holes are added, each with its complete source argument and matching node:

- `WeilConjectures.exactFunctorGoodTruncations`, node
  `lem-trf-exact-functor-good-truncations`, in
  `Sheaf.Paper.ExactFunctorGoodTruncations`.
- `WeilConjectures.quotientGermTower`, node `lem-trf-quotient-germ-tower`, in
  `Sheaf.Paper.QuotientGermTower`.

This is a decomposition of the upper theorem, with one original hole closed and
two lower holes added, rather than an axiom-free proof of the complete result.
Both new holes are strictly partial steps: the first concerns arbitrary exact
functors and truncations only; the second concerns finite germs and strict tower
naturality only. Neither asserts boundedness, the completed realization, Roos
comparison, or its derived naturality. No definition contains a hole.

## No longer needed

The following private proof imports are removed from the item module:
`Sheaf.AlgebraicGeometry.ProEtaleConstantExact`,
`Sheaf.Paper.IntegralOperationsPreserveConstructible`,
`Sheaf.Paper.PointProEtaleSectionsExact`,
`Sheaf.AlgebraicGeometry.ProEtaleClassicalStalk`,
`Sheaf.CategoryTheory.StrictRoosComparison`, and
`Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`.
Exact finite pullback, point sections, and stalk facts remain available through
existing imports and the proof modules actually used.

The direct proof route does not need
`lem-pur-integral-operations-preserve-constructible`,
`lem-trf-point-pullback-representative-diagram`, or
`lem-weil-strict-roos-comparison`; their obsolete top-level tool approvals are
removed from the parent node. The old approval for
`prop-weil-pbc-proetale-constant-exact` is also removed: the finite pullback step
uses `lem-pur-coefficient-pullback-exact`, the exactness theorem for the actual
`coefficientProEtaleModulePullback` in `integralOperationsLevelPullback`.
The ambient point-fibre functor and its defining
factorization suffice without first proving constructibility of pullback.
The already proved natural Roos comparison gives precisely the scalar map, so
neither a new representative diagram nor strict derived-limit comparison is
required. `lem-weil-proetale-countable-products-exact` is not used directly:
Roos quasi-isomorphisms take values in modules, where products are exact.
The direct dependencies `def-weil-derived-complete-integral-detailed`,
`def-weil-proetale-geometric-stalk`, `lem-cbc-proetale-classical-stalk`,
`lem-trf-proetale-pullback-stalk-coherence`, and
`lem-weil-point-proetale-sections-exact` move to the bound/germ steps or the
existing stalk/sections helper modules; they are still needed transitively.
No module is withdrawn, and no claim of globally pruning these shared
dependencies is made.

## Where the brief, the DAG or earlier work was wrong

The original planned route introduced a constructibility-preservation detour
although the displayed realization is an ambient derived-category assertion.
The existing explicit Roos natural isomorphism and scalar-map uniqueness give a
shorter route while retaining the prescribed comparison arrow. No original
statement is disputed or weakened. In particular the interval remains a bound
on cohomology, not on terms or Tor amplitude; the coinciding-boundary case is
proved with its genuine homology term.

The existing reduction-tower node locates Flat resolutions and Derived pullback
in `sites-modules.tex`; the local Stacks tag database places Tags 06YL and 06YV
in `sites-cohomology.tex`. The new bounds node cites the latter source. The
existing node is not edited by this packet.

## New nodes

`lem-trf-exact-functor-good-truncations` records exact-functor compatibility with
both canonical good truncations and their boundary arrows. Its proof is the
kernel/cokernel comparison construction of Stacks Tag 0118. The equations are
needed to retain the original naturality normalization.

`lem-trf-integral-quotient-cohomological-bounds` records the proved transport of
the defining uniform derived-reduction support interval to the actual quotient
complex of any given good representative. It uses
`unrestrictedTowerResolutionIso` for the identity resolution, the given q, and
exact scalar restriction; it introduces no additional hole.

`lem-trf-quotient-germ-tower` records just the finite section-to-stalk germ
normalization, pullback-unit germ formula, and their degreewise strict tower
isomorphism. Its proof uses the initial identity-point neighbourhood, the
published pullback-stalk coherence, and compatibility of reduction on germ
representatives. It asserts no completed-fibre or Roos result. All three nodes
retain the parent unit `sk-thm-trace-transport`; the unit route is preserved.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
