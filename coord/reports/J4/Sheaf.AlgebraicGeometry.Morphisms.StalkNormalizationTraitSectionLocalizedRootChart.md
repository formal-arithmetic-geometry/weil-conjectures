## What changed

Replaced the proof of
`AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_trait_section_localized_root_chart`
with a complete Lean combination of three separately stated geometric steps. Its signature and
visibility are unchanged. Three proof-only imports were added:
`StalkNormalizationTraitDivisorCharts`, `RootProductChartStalkLocalization`, and
`TraitDivisorChartSectionGenericFactor`, all under `Sheaf.AlgebraicGeometry.Morphisms`.

The first supplies a root product chart using an actual trait uniformizer. The second selects
one factor and localizes its base and root algebra, proving the required stalk-map conclusion.
The third takes the same supplied chart and selected factor index and constructs its generic
section factor. The original proof explicitly combines these conclusions with the common
exponent `e k`. No definition data is chosen from an unproved existence theorem: every choice
occurs only inside a theorem proof and ultimately its existential conclusion.

Source read: Stacks 0EYH, 0EYI (the preliminary paragraph before parts (1) and (2)), and 0EYJ
(the trait paragraph), at their official online pages. The local checkout contains only the
literature indexes. The unit `sk-prop-input-spreading` and its trait and section steps were read;
the reduction keeps that route, without invoking rational-point or splitting assumptions.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_trait_section_localized_root_chart`
(node `lem-sbc-stalk-normalization-trait-section-localized-root-chart`). No sorry remains in the
assigned module. This is a decomposition, not a complete proof of the geometric input.

Added three named holes, each exactly `:= by sorry` in its own new module:

- `AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_trait_divisor_charts`
  (`lem-sbc-stalk-normalization-trait-divisor-charts`).
- `AlgebraicGeometry.Scheme.rootProductChart_stalk_localization`
  (`lem-sbc-root-product-chart-stalk-localization`).
- `AlgebraicGeometry.Scheme.GaloisCover.trait_divisor_chart_section_generic_factor`
  (`lem-sbc-trait-divisor-chart-section-generic-factor`).

The three are strictly separate parts: an affine chart without either desired conclusion;
a general chart-to-stalk result with no section or generic cover; and a generic factor result
assuming a supplied chart, without a local root algebra or stalk map. All four files compile
with the prescribed compiler. The dry-run result is recorded by the delivery tool.

Edge cases checked mathematically: an empty normalization has no x; a zero product chart
cannot have a point above x and supplies no index k; positive exponents make the root
polynomials monic; f in y makes its localized image lie in the base maximal ideal; monicity
makes the prime over that maximal ideal maximal. A common residue-field extension supplies
the points in the indicated pullbacks. The closed fibre of an essentially etale local map
is a field, giving the maximal ideal extension used in the stalk step. The section pulls the
base uniformizer back to a uniformizer in its unramified DVR extension. None of these steps
identifies a localized root algebra with the whole root algebra.

## No longer needed

Removed unused RingHom.Flat and Localization.AtPrime.Basic imports from each of the two new
modules StalkNormalizationTraitDivisorCharts and TraitDivisorChartSectionGenericFactor.
No old proof dependency was removed. The original node had no proof dependencies and the original module had only statement
imports, which remain unchanged. The existing `StalkNormalizationTraitCharts`,
`TraitGenericNormalizationCharts`, `TraitGenericRootModel`, and `TraitGenericPuncturedRootChart`
were inspected but not imported: their statements do not retain the required equality of the
chart equation with a pulled-back trait uniformizer. No module is claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

The assigned node records three non-elementary proof steps with empty `uses` and empty
`proof_deps`. Thus no existing stated dependency implements those steps, despite the general
brief describing such dependencies. The delivery makes those steps explicit instead of
moving the full statement under another name. The new affine chart retains the missing divisor
compatibility; this is why the existing weaker chart statement cannot directly supply it.

LeanSearch returned Internal Server Error and was recorded as unavailable. Loogle and actual
Mathlib grep searches found no matching theorem; semantic search returned standard-etale
presentation lemmas, not a tame geometric chart. Blueprint searches for tame root charts and
0EYI returned no matching blueprint node. No statement is disputed and no interface is changed.

## New nodes

`lem-sbc-stalk-normalization-trait-divisor-charts` records construction of a compatible affine
chart with common equation rho(varpi), before either localization or generic factor extraction.
Its source is 0EYJ, 0EYG and 0EYH. It preserves the divisor equation missing from existing charts.

`lem-sbc-root-product-chart-stalk-localization` records the purely local extraction of a factor
from a supplied etale product chart, with the flat local map and extended-ideal equality.
Its source is the pointed chart construction of 0EYH and 0EYI.

`lem-sbc-trait-divisor-chart-section-generic-factor` records the transverse section restriction
of any supplied compatible chart and any selected factor. Its source is the preliminary
paragraph of 0EYI and the trait reduction of 0EYJ.

Each new node has a corresponding one-theorem module, a full proof in words, actual search
records and the same chapter/unit as the assigned item. The existing item's proof dependencies
now name precisely these three steps. There are no change records or forced adaptations.


## Second reading by J4

1. Compared the delivered module with the repository using diff: its existing signature is
byte-for-byte unchanged; only its proof and three plain proof imports change. A field-by-field
comparison of the existing node shows changes only to proof, proof_deps and proof_origin.
No definition, existing statement, or visibility changes; no change record is needed.

2. All four files compile with lcompile.py --all, without warnings. A scratch copy with explicit
#print axioms for all four declarations reports only propext, Classical.choice, Quot.sound and
sorryAx. Exactly the three listed new named theorems contain sorry; no axiom, unsafe, opaque,
extern, implemented_by or definition containing sorry occurs. No data definition was added.

3. Read all three new signatures, docstrings and nodes against Stacks 0EYH, 0EYI and 0EYJ.
The compatible chart exists by tame ramification and adjustment of a unit multiple of the divisor
by adjoining its roots etale locally. Stalk localization selects one product factor at a point
above both x and y; integrality makes its prime maximal, and the etale local base map gives the
ideal equality. For the generic factor, the section pullback chart has an unramified DVR local
ring; the actual trait uniformizer remains a uniformizer. Base change to its fraction field
preserves all factors and their open inclusions. The generic restriction is Z by normalization
comparison. Empty covers have no x, zero products have no chosen factor, and e=1 is allowed;
positive exponents give monic polynomials. Each lemma is strictly one part of the argument.
Independent msearch queries used etale stalk flatness, Kummer equations with a specified divisor
generator, and DVR extensions with the same uniformizer. Semantic search and Loogle found no
replacement; grep found Flat.stalkMap as a tool for the eventual localization proof, not the whole
statement. The loogle stalkMap query was unresolved, so its empty result was not evidence.
Read the existing trait charts, normalization charts and punctured chart signatures directly:
none retains the required equation rho(varpi). No split-off hole closes in a short application.

4. The proof combines chart construction, localized stalk extraction and section restriction;
the same selected k and exponent e k occur in both final conclusions. It follows the trait and
section steps of sk-prop-input-spreading, with no rational-point or splitting assumption.
The unit's realized lists are empty in the repository; this item fills no pre-existing realized
entry and changes no unit route. All three added plain imports are used. Old proof_deps was empty,
so No longer needed has no old node to list. I removed two unused public imports from each of the
two new geometric modules and recompiled: RingHom.Flat and Localization.AtPrime.Basic. These were
not needed by either signature or proof. No globally pruned module is claimed.

5. All four nodes agree with their Lean declarations, and each new node has the required source,
complete proof in words, searches, creation, blueprint, unit/chapter and verbatim Lean record.
The existing node names exactly the three helper nodes used by the reduction. This closes one
original hole and adds three strictly narrower holes, net minus two: a decomposition only.

Second reading changed four unused import lines and this report. Statements and proofs retained.
