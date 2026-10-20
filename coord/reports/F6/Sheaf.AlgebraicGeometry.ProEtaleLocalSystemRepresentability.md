## What changed

Prove `AlgebraicGeometry.Scheme.proEtale_localSystem_representability` from local
classicality, a size-explicit etale realization, fpqc-cover universe transport, fpqc
separated/valuative descent, and separated-etale schemehood. Private proved helpers
establish separatedness and the full valuative criterion for arbitrary coproducts
of copies of a scheme, and transport these properties across presheaf isomorphisms.
The final isomorphism is an isomorphism of presheaves on the original site.
The original pro-etale cover is proved fpqc by extracting a precoverage
refinement at the identity object and applying QuasiCompactCover.of_hom;
only transport of an arbitrary fpqc cover to the enlarged universe is postponed.

The new realization module bundles the existing enlargement maps as a functor,
with its identity law proved from the colimit equations. The site functor is factored through this wrapper with an irreducible boundary
to prevent repeated colimit unfolding; its object and arrow maps are unchanged.
All existing signatures are unchanged. See change record
`coord/changes/F6-proEtale-universe-lift-boundary.md`. The attempted change
to `SchemeUniverseEnlargement` was removed after preflight identified B3 as its
current holder; no existing module other than the assigned item is adapted.

## Proved and sorry left

Existing holes closed:
- `AlgebraicGeometry.Scheme.proEtale_localSystem_representability`
  (`lem-a1-proetale-local-system-representability`).

New holes, each in its own module and with a source and proof in its docstring:
- `AlgebraicGeometry.Scheme.fpqc_cover_universeLift`
  (`lem-a1-universe-enlarged-proetale-cover`).
- `AlgebraicGeometry.AlgebraicSpace.etaleSheaf_universeEnlarged_realization`
  (`lem-a1-universe-enlarged-etale-realization`).

The assigned module has zero remaining holes. The three-module packet has two
holes, both added. One existing hole closed and two added is a decomposition
with net minus one holes closed, not a proof of the full import closure.
The existing `schemeUniverseDiagram_hasColimit` and `schemeUniverseLiftMap_comp`
holes remain in their unchanged dependency module (`def-trf-scheme-universe-enlargement`).
The coproduct and presheaf transport helpers contain no holes. The new cover
lemma is a universe-transport result about arbitrary fpqc coverings alone.
The extraction from CoversTop is completely proved in the assigned module. The new realization
lemma concerns every etale sheaf, with no locally Noetherian or covering
hypothesis, and does not assert separatedness, schemehood, or a valuative
criterion. Neither repeats the assigned conclusion.

## No longer needed

Removed direct proof imports:
- `Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesUnit`;
- `Sheaf.AlgebraicGeometry.ConstantSheafSetsRepresentable`;
- `Mathlib.CategoryTheory.Adjunction.Limits`;
- `Sheaf.AlgebraicGeometry.EtaleSheafAlgebraicSpaceRealization`.

The realization module imports the classical-sheaves unit and constant-sheaf
representability modules because they remain part of its proof plan; they are not
claimed globally pruned. The original small-universe realization theorem cannot
be applied directly to an arbitrary `Type (u + 1)` valued sheaf, and is replaced
in the assigned proof by its explicit enlargement counterpart. The direct
closed-immersion-base-change node is realized by Mathlib stability in the proved
Yoneda transport helper; no extra Sheaf import is needed for this Mathlib leaf. Scheme
coproducts and fibre products remain used through Mathlib and the clopen morphism
lemma. The direct ProEtaleSiteComparison import is retained for the unit route.
No unit-level statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original realization API handles small-valued etale sheaves and lifts their
section sets. It does not give a realization of arbitrary large-valued etale
sheaves over the specified enlarged base. Likewise the pro-etale site API does
not yet transport fpqc covers through the affine-colimit enlargement. These are
the two separate mathematical results recorded by the new nodes.

The retained packet and all three delivered modules were checked using `lcompile.py --all`.
The provider interruptions repeatedly reset the launcher split-policy reference
clock: the retained start 1792424380.6380832 was later replaced by
1792428211.2188048, with subsequent dry runs reporting one or five elapsed
minutes. No budget metadata was edited. The earlier compile-server outage
was not reproduced. The two source results remain separate mathematical
lemmas; their separation is required by the missing universe-transport API,
not by a compilation timeout or by moving the assigned statement unchanged.

## New nodes

`lem-a1-universe-enlarged-proetale-cover`: canonical enlargement transports an
arbitrary fpqc covering family to an fpqc covering. Source: the fpqc-cover definition
and affine gluing. The empty base and empty index case is allowed; no
quasi-compactness of individual covering arrows is asserted.

`lem-a1-universe-enlarged-etale-realization`: the size-explicit generator quotient
construction of Stacks 0GF6, with its size footnote, and comparison/restriction
from Bhatt--Scholze 5.1.1, 5.1.2, and 5.4.1. Empty and infinite sheet sets are
allowed. Its local conclusion is an isomorphism on all schemes over the enlarged
cover member, sufficient to transport separatedness and valuation lifting.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
