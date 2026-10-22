## What changed

The normalization theorem is reduced to three fixed-resolution comparisons: naturality of raw evaluation, compatibility with chart restriction, and the cocycle-class identity as an equality of homomorphisms; its value at each raw class gives the original scalar formula. The combining proof also establishes coefficient compatibility and identifies the sheafification lift with the source library's constructed canonicalComparison.

The normalization constructions move, preserving their mathematical objects, to RawRestrictedClassNormalizationData. The original module publicly reexports this module. The pushed-forward complex now has an explicit type and is a regular definition with the same construction. Four aliases become abbreviations with their formulas preserved: normalizationIota, normalizationRawCoefficient, normalizationRestrictedCoefficient and normalizationHigherCoefficient. This avoids costly conversion through nested sheaf constructions. The transported presheaf uses a generic conjugation constructor with the same object family and maps. This permits the three comparison statements to refer to the prescribed constructions without an import cycle. No target statement changes. There are no existing Lean importers of the item module or external users of the moved normalization declarations. The change record is coord/changes/F2-raw-normalization-resolution-data.md.

Generic private lemmas for adjunction, shift, homology, evaluation and transport of isomorphisms keep the concrete sheaf calculations within a small categorical API. The combined proof and all four supporting modules have compiled within the 60-second per-file limit. The final assembly keeps the isomorphism witness within the first conjunction branch and uses a generic elementwise class lemma. This version compiled in 47.5 seconds before a formatting-only fix.

## Proved and sorry left

The original hole is AlgebraicGeometry.Etale.rawRestrictedClassNormalization. Its hole is closed by a combining proof from the three comparison statements below; this is a decomposition. The original supporting theorems remain proved. Raw coefficient compatibility and canonical-class coefficient compatibility are proved from functor and adjunction naturality.

Three new named theorem holes remain:

- AlgebraicGeometry.Etale.rawRestrictedResolution_naturality (node lem-weil-pbc-raw-restricted-resolution-naturality).
- AlgebraicGeometry.Etale.rawRestrictedResolution_restriction (node lem-weil-pbc-raw-restricted-resolution-restriction).
- AlgebraicGeometry.Etale.rawRestrictedResolution_class (node lem-weil-pbc-raw-restricted-resolution-class).

The packet closes one upper hole and adds these three holes: net -2 holes closed. This is a decomposition into strictly smaller comparisons, not proof progress in the sorry ledger. The data module has zero holes. No definition contains sorry or selects data from an unproved mere-existence statement. The comparison statements apply in degree zero, to the zero coefficient sheaf and to empty charts; the restriction and naturality statements include identity arrows.

## No longer needed

The private imports Sheaf.Paper.SiteHigherDirectImageSheafifiedPresheaf, WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial and WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact are removed. RawRestrictedCohomologyComparisonIsIso remains a private proof import in the main module. All original public imports are reexported through the data module.

The lift's invertibility follows from canonicalComparison and its exact class formula, so the planned proof through lem-weil-pbc-site-higher-direct-image-sheafified-presheaf is unnecessary here. Its proof edge and obsolete tool-use entry are removed from the parent node; the preexisting statement-dependency entry is retained. No global withdrawal of that node or its module is claimed.

The obsolete top-level tool-use entry for lem-weil-pbc-dplus-injective-representative is also removed. The parent proof no longer directly uses lem-weil-pbc-dplus-injective-representative, lem-weil-pbc-cohomology-pullback-functorial or lem-weil-pbc-etale-base-change-continuous. The fixed chosen resolution and the three comparison lemmas replace that route. The other former direct dependencies concerning inverse image, direct image, sheafification, restricted evaluation, K-injective representatives and cohomology remain needed through the data and comparison nodes. No source-library declaration or module is removed, and the unit's statement and proof route remain in place.

Comparing the old and new dependency graph below this item, the following nodes cease to be reachable: def-constructible-constant, def-pc-ext, lem-weil-pbc-cohomology-pullback-functorial, lem-weil-pbc-constant-pullback-composition-coherence, lem-weil-pbc-constant-pullback-identity-coherence, lem-weil-pbc-ext-exact-functor-composition-comparison, and lem-weil-pbc-ext-exact-functor-identity-comparison. This is pruning of this item's planned argument; uses by other declarations and targets are retained, and no Lean file is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The first preflight found two packet metadata mistakes: LeanFinder and Loogle count as one search kind, and lean.statement omits the noncomputable modifier. LeanSearch was then run and recorded for all four new nodes, and their signature records were synchronized with the declaration parser.

The available cohomology-pullback functoriality result describes Ext pullback; it does not provide the fixed-resolution restriction square needed by the specified normalization maps. That square is stated explicitly in rawRestrictedResolution_restriction, with the sections triangle and localization unit as its proof dependencies.

An invertible sign preserves cycles and boundaries. Equality of the pinned comparison maps also requires compatibility of the actual shift and adjunction comparisons. The cocycle-class statement records that compatibility instead of inferring it from invertibility of a sign.

A dependency DFS finds a preexisting reachable DAG cycle: lemma-weil-pbc-derived-exchange-replacement -> lem-weil-pbc-derived-exchange-termwise -> lem-weil-pbc-derived-exchange-bounded-comparison -> lemma-weil-pbc-derived-exchange-replacement. The identical cycle exists in the unmodified repository graph; this delivery adds no cycle. These unrelated nodes are reported for maintainer repair and are not edited here.

## New nodes

def-weil-pbc-raw-restricted-normalization-data: the prescribed constructions and their already proved supporting theorems.

lem-weil-pbc-raw-restricted-resolution-naturality: raw evaluation and restriction on section homology.

lem-weil-pbc-raw-restricted-resolution-restriction: cohomology pullback and restriction on section homology.

lem-weil-pbc-raw-restricted-resolution-class: the section cocycle and its canonical derived-adjunction class.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
