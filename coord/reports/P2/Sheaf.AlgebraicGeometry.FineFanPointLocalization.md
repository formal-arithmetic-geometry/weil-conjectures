## What changed

Replaced the sorry in `AlgebraicGeometry.FineFan.fineFan_point_localization`
with a complete Lean reduction to two smaller, named chart lemmas. Existing
public declarations, definitions, signatures and public imports are unchanged.
No existing module other than the item is edited.

The proved argument constructs a smallest neighborhood by transporting a basic
open through a fine chart. It identifies membership with specialization,
proves the germ bijective using the terminal object in the opposite
neighborhood category, proves sharpness after restriction by a final-functor
stalk isomorphism, and proves uniqueness from the injectivity assertion of
`affine_hom_universal`. The monoid minimal-neighborhood theorem supplies the
chart localization equality; contraposition applied to its intersection formula
gives the inclusion-of-primes formula. Finally, normalization identifies the
single-chart affine models for every chart, transporting each full sheafed-space
square to the uniquely chosen isomorphism.

The two split statements concern actual chart-stalk coordinates and construction
of a normalized affine model in one specified chart. Their signatures explicitly
use the actual germs and global-section transport; there are no surrogate data
choices or changed definitions. The first does not mention neighborhoods or
morphisms of spaces. The second assumes a fixed smallest neighborhood and a
fine stalk and constructs only a single-chart model; it asserts neither
uniqueness nor the all-chart formulas. Thus neither restates the item.

Validation: all three final import-pruned modules compile cleanly through
lcompile.py --all: FineFanChartMinimalAffine in 3.4 s,
FineFanChartStalkCoordinates in 3.3 s, and FineFanPointLocalization in 5.8 s.

## Proved and sorry left

Original holes: 1. Closed by reduction: 1, in
`AlgebraicGeometry.FineFan.fineFan_point_localization`
(node `lem-trf-fine-fan-point-localization`). The item now has zero textual holes.
This is a decomposition, not a completed proof of the underlying sheaf theory.

Added holes: 2, each the complete body of a public theorem:

- `AlgebraicGeometry.FineFan.fineFan_chart_stalk_coordinates`, in
  `Sheaf.AlgebraicGeometry.FineFanChartStalkCoordinates`, node
  `lem-trf-fine-fan-chart-stalk-coordinates`.
- `AlgebraicGeometry.FineFan.fineFan_chart_minimal_affine`, in
  `Sheaf.AlgebraicGeometry.FineFanChartMinimalAffine`, node
  `lem-trf-fine-fan-chart-minimal-affine`.

There are no other sorry occurrences in this delivery. Both admitted statements
have full sourced proof plans in their docstrings and matching DAG nodes. The
textual hole delta of the delivery is 1 closed minus 2 added = -1; no claim of
positive net sorry-ledger progress is made.

## No longer needed

Removed the item's proof-only imports of
`Sheaf.AlgebraicGeometry.AffineFanLocalizationSections` and
`Mathlib.Topology.Sheaves.SheafCondition.Sites`.
The direct sections computation and the sheaf extension are not used by the
proved assembly: a terminal neighborhood computes the germ, and the affine
sheaf construction is isolated in a smaller statement.

The original direct proof dependencies
`lem-trf-affine-fan-localization-sections`,
`lem-trf-integral-sharpening-group-exactness`, and
`lem-weil-pbc-sheaf-morphism-on-basis` move into the proof plans of the two
new nodes. They remain needed there; they are not globally pruned. No existing
node or module is withdrawn, and no source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

No statement error or false lemma was found. The monoid-neighborhood lemma has
exactly the intersection, smallest-open and localization formulas needed. The
affine sections theorem is about affine spaces, whereas this item's conclusion
uses actual stalks and transported sections of an arbitrary chart: that
transport and its numerator normalization are isolated explicitly. Likewise,
the prime correspondence and compatible localized-sharpening section maps are
substantial sheaf arguments, now isolated in the single-chart construction.

Mathlib's `PresheafedSpace.restrictStalkIso` API requires arbitrary colimits in
the coefficient category, while the framework provides filtered monoid
colimits. The proved restriction-sharpness helper uses the underlying
`Functor.Final.colimitIso` directly, requiring only those available filtered
colimits; no shared instance or definition is changed.

Read ILO VIII 3.1.1--3.1.10, printed pp.98--100, and the current latest blueprint
unit `sk-i-curve-zero`. Its realized route is unchanged. Checked the new
statements for a trivial monoid/empty generating tuple, group charts, empty
and maximal primes, and nonsharp chart monoids. No saturation or torsion-free
hypothesis is introduced. Searches through msearch.py (LeanFinder, Loogle,
grep), project rg, and Mathlib source found no exact replacement for either
remaining chart assertion.

## New nodes

`lem-trf-fine-fan-chart-stalk-coordinates` isolates the actual-stalk transport,
the canonical numerator formula and finite integral sharpening (original
steps 2--3). Its proof uses the existing affine sections, monoid-neighborhood
and integral-sharpening statements.

`lem-trf-fine-fan-chart-minimal-affine` isolates the single-chart prime
correspondence, localized-sharpening comparison, extension of section maps
from a basis and normalized affine model (original steps 4--7). It uses the
first new node for its actual-stalk coordinates. The parent proves independence
of this chart and uniqueness itself.

No change record is required: the item's existing public interface is identical,
and only the item, new modules, and their DAG nodes are changed.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
