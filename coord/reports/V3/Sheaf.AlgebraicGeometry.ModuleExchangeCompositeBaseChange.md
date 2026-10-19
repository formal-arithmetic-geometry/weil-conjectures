## What changed

Proved AlgebraicGeometry.Etale.moduleExchange_composite_baseChange, including both
the natural-transformation equality and the componentwise isomorphism criterion.
The public statements and moduleInverseImageCompIso definition are unchanged.

Private helpers implement the inverse-image composition calculus abstractly, avoiding
unfolding derived functors in the categorical pasting calculation. Their proofs reuse
the argument already proved privately in EtaleDerivedBaseChangeLocalTransport,
specialized here to ModuleCat Λ. The module system does not export those existing
private helpers, so the argument is instantiated locally rather than importing that
large abelian-only theorem. The exact derived composition comparisons satisfy
associativity by mapDerivedCategoryNatIso_trans, its whiskering laws, and
mapDerivedCategoryCompIso_assoc applied to upperStarComp_assoc'. Square pasting then
uses three associativity rewrites, and the two existing mate-pasting laws give the
specified exchange. Cancellation of the outside isomorphisms proves the criterion.

Added the proof-only import
WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate. Removed the
two unused public imports listed below. No other library module is changed; no new
public declarations, new nodes, or unproved intermediates are added. Updated the
existing node's proof and proof_deps to describe the actual coherence calculation.
Change record: coord/changes/V3-module-exchange-composite-import-pruning.md.

## Proved and sorry left

Closed 1 of 1 original holes:
AlgebraicGeometry.Etale.moduleExchange_composite_baseChange
(node lem-fin-module-exchange-composite-base-change).
Added 0 holes; 0 sorries remain in the delivered module. No statements were split off.
All new private helpers are proved. The construction moduleInverseImageCompIso is
unchanged and contains no hole.

Validation: lcompile.py compiled the final pruned module cleanly in 5.7 seconds.
The two unchanged direct importers were individually compiled against this sandbox's
compiled module: EtaleGenericDirectImageExchange (4.3 seconds) and
GabberOpenImmersionSheafFiniteness (5.3 seconds), both clean. Their temporary sandbox
copies were removed after checking byte-for-byte equality with the original files;
no consumer is part of the delivery. Original public signatures were compared
verbatim and are identical. The required delivery probe checks all added constants,
including the private helpers, for axioms and direct sorry usage.

## No longer needed

Removed public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact:
no use of etaleInverseImageModulesExact or its additional module/ring comparison data
is required. Exactness instances for upperStar on ModuleCat are already available
through ExactUnboundedExchange's generic coefficient-category API. Removed
prop-weil-pbc-inverse-image-modules-exact from proof_deps and the old tool_uses entry.
Its statement dependency remains: the mathematical meaning of the exact inverse
image used in the statement is unchanged.

Removed public import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets: neither
abelianDerivedBaseChangeArrow nor any other declaration in this module is used.
The unbounded module exchange is handled directly by ExactUnboundedExchange.

All other original imports are retained and used. The route still uses
lem-weil-pbc-square-iso-pasting's ordinary composition coherence,
lem-weil-pbc-localization-universal-property via the proved derived coherence API,
lem-weil-pbc-mate-pasting, lem-weil-pbc-mate-whisker, and def-kun-unbounded-exchange.
No claim is made that a removed import is globally unreachable: other parents may
still use it.

## Where the brief, the DAG or earlier work was wrong

No statement error. The plan needlessly passed from abelian-sheaf comparisons to
module maps: squareUpperStarIso and upperStarComp_assoc' already support any suitable
abelian coefficient category, including ModuleCat Λ. Derive that generic coherence
equation directly. The proof still realizes the square-pasting, localization,
mate-pasting and invertible-factor-cancellation steps, with no change to the unit route.

Searches: msearch.py LeanFinder for derived exchange horizontal pasting found only
generic categorical base change and scheme pullback-composition results; Loogle found
mateEquiv_vcomp. Repository rg found the exact generic proof pattern in
EtaleDerivedBaseChangeLocalTransport, and the proved coherence API in
WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate. No existing
public theorem directly proves the item. No new statement requires a node.

Edge cases: the categorical argument needs only CommSq, so identity horizontal maps,
empty schemes, the zero ring and the zero complex require no additional assumption.
The ChosenCartesianSquare hypotheses and all universes remain exactly as supplied.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
