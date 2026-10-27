## What changed

Proved `AlgebraicGeometry.Scheme.trfEtaleStructureRing_isSheaf` by pointwise gluing
using the existing set-valued etale structure sheaf theorem. Proved
`AlgebraicGeometry.Scheme.scheme_etale_invertible_comparison` from the stated normalized
section functor, full faithfulness and essential surjectivity. Mathlib's `asEquivalence`
retains exactly that forward functor, so every required scalar, morphism, unit,
restriction, identity and composition formula transfers directly.

The shared definitions and the proved structure-ring sheaf condition move unchanged
in name, type and data to `Sheaf.SixFunctors.TraceFormula.SchemeEtaleLineDefinitions`.
The item publicly re-exports that module. This permits the item to import its stated
normalized-comparison dependency without a cycle. Two new modules contain proved
full-faithfulness and essential-surjectivity helper theorems, with matching DAG nodes.

The full-faithfulness proof conjugates the existing tensor-extension Hom bijection by
componentwise linear isomorphisms. The essential-surjectivity proof applies the existing
transition-units and effective-gluing statements; frame cancellation supplies all
pointwise cocycle and diagonal equations. Empty covers and empty schemes are allowed.

The complete sandbox and all seven unchanged direct consumers compile together
in import order, each under 60 seconds. The delivered files take 7.1 s (data),
25.1 s (essential surjectivity), 20.5 s (full faithfulness), 8.8 s (normalized
comparisons) and 26.1 s (the final theorem). Consumer times range from 15.5 s to
43.8 s. The consumers checked are `AbelianVariety.PolarizationCalculusOverField`,
`AlgebraicSpaceInvertibleDescent`, `AlgebraicallyTrivialLineMultiplicativity`,
`NodalRelativeDualizingLine`, `SpaceMeromorphicGenericChartModel`,
`RegularSpaceDivisorLineDictionary` (all under `Sheaf.AlgebraicGeometry`) and
`Sheaf.TraceFormula.AmpleSchemeTestLinePreparation`. The unchanged consumer copies
were removed from the packet after verification.

## Proved and sorry left

Closed both original holes:
- `AlgebraicGeometry.Scheme.trfEtaleStructureRing_isSheaf`
  (`def-trf-scheme-etale-line-comparison-data`; moved from the item's original node).
- `AlgebraicGeometry.Scheme.scheme_etale_invertible_comparison`
  (`lem-trf-scheme-etale-invertible-comparison`).

Added zero holes. Both new helper theorems are proved, not split-off holes:
- `AlgebraicGeometry.Scheme.etale_line_sections_fullFaithful`
  (`lem-trf-etale-line-sections-full-faithful`).
- `AlgebraicGeometry.Scheme.etale_line_sections_essSurj`
  (`lem-trf-etale-line-sections-essentially-surjective`).

The adapted normalized-comparison file retains its pre-existing, untouched hole
`AlgebraicGeometry.Scheme.etale_line_sections_normalized_comparisons`
(`lem-trf-etale-line-sections-normalized-comparisons`). Existing imported mathematical
inputs may still contain holes; no claim of axiom-free transitive closure is made.

## No longer needed

Removed the item's direct private imports of:
- `WeilConjectures.AlgebraicGeometry.Descent`
- `WeilConjectures.AlgebraicGeometry.ZariskiEtaleInclusionMorphismOfSites`
- `Sheaf.AlgebraicGeometry.FpqcFinerThanEtale`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `WeilConjectures.AlgebraicGeometry.EtaleQuasiCoherentDescent`
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`

The first five belong below the stated input lemmas; the last is already publicly
available through the retained projection-formula import. The data module retains
only the original public imports and the private inputs used by its definitions and
sheaf proof. The item replaces the original imports with a public re-export of these
data and private imports of the three proof pieces.

All five original proof-dependency nodes remain used transitively, through the two
proved helpers and normalized comparisons. None is claimed globally pruned.
Obsolete direct tool-use approvals were removed from the item's node; the normalized
comparison and helper nodes carry the actual dependency route. The unit route stays.

## Where the brief, the DAG or earlier work was wrong

The planned normalized-comparison input imported the item for its shared definitions.
Thus adding the required proof import directly closes an import cycle. Separating data
from the equivalence theorem repairs this without changing any mathematical statement.

The general sheaf-composition lemma requires limits at the site's object universe;
`CommRingCat.{u} -> RingCat.{u}` has only the available small-limit instance. Its direct
application fails to synthesize `PreservesLimitsOfSize.{u, u + 1}`. The pointwise proof
avoids a universe-small sheafification or limit assumption entirely.

## Forced adaptations

`Sheaf.SixFunctors.TraceFormula.EtaleLineSectionsNormalizedComparisons` is held by S2.
Only line 8 changes: its public import of the comparison item is replaced by a public
import of `SchemeEtaleLineDefinitions`. No declaration, proof or other import changes.
With the original import and the item's required proof import, the import checker says:
`NO: Sheaf.SixFunctors.TraceFormula.EtaleLineSectionsNormalizedComparisons already reaches
Sheaf.SixFunctors.TraceFormula.SchemeEtaleInvertibleComparison; importing it from
Sheaf.SixFunctors.TraceFormula.SchemeEtaleInvertibleComparison closes a cycle`.
The original-import negative compile additionally reports:
`the modules import one another in a cycle:
Sheaf.SixFunctors.TraceFormula.EtaleLineSectionsNormalizedComparisons,
Sheaf.SixFunctors.TraceFormula.SchemeEtaleInvertibleComparison`.
Restoring the single adapted import compiles the normalized-comparison module in
6.3 seconds. This is the forced adaptation of the item's separation of its data
from its theorem.

## New nodes

`def-trf-scheme-etale-line-comparison-data` records the original shared definitions in
their new module, including the proved structure-ring sheaf condition. Their data,
names and signatures are preserved; only the theorem proof is filled.

`lem-trf-etale-line-sections-full-faithful` records the proved Hom-bijection transport,
using the declared tensor-extension Hom theorem for quasi-coherent modules.

`lem-trf-etale-line-sections-essentially-surjective` records the proved descent argument,
using the declared transition-units and effective-gluing theorems. It does not assume
the equivalence being proved or the general Zariski-etale quasi-coherent equivalence.

Change record: `coord/changes/trf-etale-comparison-definitions.md`.

## Forced adaptations

### Sheaf.SixFunctors.TraceFormula.EtaleLineSectionsNormalizedComparisons
NOT FORCED: the original compiles unchanged against the changed dependencies. Adapted module compiled in the delivered set; the reader judges whether the change is right.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
