## What changed

Reduced `exists_affineCohomologyEtaleModuleRealization` to two separate geometric
compatibility results. The combining proof constructs the affine natural isomorphism,
extends it using cover-density and the sheafification universal property, normalizes it
using the source library canonical comparison and its actual raw-class formula, proves affine linearity using coefficient naturality and the
scalar-endomorphism theorem, and proves linearity everywhere by sheaf separation.

Extracted the four existing comparison/action-evaluation definitions into
`Sheaf.AlgebraicGeometry.AffineCohomologyComparisonData` with identical signatures and
bodies, publicly re-exported from the original module, so the two compatibility modules
can use them without an import cycle. Change record:
`coord/changes/affine-cohomology-comparison-data.md`.

The current work also repairs expensive evaluation interfaces in
CoherentHigherImageClasses: construct the additive raw equivalence once, expose its
bijectivity and cancellation API. The higher-image abbreviation is unchanged.
Every mathematical map remains the original constructed map. The inverse is equal
to the original inverse by injectivity of raw evaluation. This unclaimed module's
only existing consumer is the item; all new consumers are in the packet.
Change record: `coord/changes/coherent-higher-image-evaluation-api.md`.

The combining proof keeps tensor restrictions as categorical morphisms through the
universe lift. The comparison interface now also bundles the raw and ordinary chart groups, their
restriction, and the already constructed composite raw-coherent equivalence, with its
proved evaluation formula and naturality API. Bundle-preserving component constructors
and generic evaluation lemmas use named private section wrappers with their literal
underlying sections. Explicit chart indices and proved application formulas keep the
large cohomology and adjunction constructions folded. These helpers are
proved privately in the item module; no proof was split across files for the time limit.
The geometric construction first gives the cohomology-class normalization by the proved
raw-evaluation cancellation API. A pointwise application of that API gives the raw
normalization. The scalar proof uses the class map directly. Its affine naturality input
is stated verbatim, avoiding a costly conversion through a predicate wrapper.

## Proved and sorry left

The item's single hole, `exists_affineCohomologyEtaleModuleRealization`, has been replaced
by a complete compiling proof from the two geometric compatibility results below.
This is a decomposition, not a net proof: two new holes remain:

- `AlgebraicGeometry.Scheme.Modules.affineRealizationRawComparison_natural`, node
  `lem-weil-pbc-affine-cohomology-raw-restriction`: only the restriction square for the
  fixed raw evaluation and fixed normalized comparison; it has no E, realization, action,
  descent, or sheaf-isomorphism conclusion.
- `AlgebraicGeometry.Scheme.Modules.exists_coherentHigherImageModuleAction`, node
  `lem-weil-pbc-coherent-higher-image-module-action`: the canonical action independent of
  any E or affine coherent comparison, with semilinear restriction and class compatibility.

Source hole count: 1 removed, 2 added. The assigned module has zero remaining holes.
`CoherentHigherImageClasses` and `AffineCohomologyComparisonData` also have zero holes.
No definition contains a hole or selects an arbitrary witness of mere existence.
All interface-extraction definitions have zero holes.

## No longer needed

The bespoke dense-subsite/sheafification-compatibility node
`lem-pc-dense-subsite-sheafification-compatibility` is unnecessary on this route: the proof
constructs the inverse by dense extension and verifies both inverse identities using
Mathlib's actual sheafification unit. The full affine object's cover-density follows from
Mathlib's `AffineEtale.Spec` cover-density by enlarging the covering sieve, so the separate
`lem-weil-pbc-affine-opens-basis` is not needed directly. The canonical scalar calculation
uses coefficient naturality of the uniquely normalized comparison rather than the entire
simultaneous arbitrary-pullback family. The normalized pullback-square dependency remains
needed in the new raw restriction lemma.

The item uses the already proved private `canonicalComparison` and
`canonicalComparison_class` from the adopted natural-comparison module through a private
`import all`. This supplies the exact sheafification isomorphism and its raw-class formula.
The item no longer extracts these facts from the large raw-restricted normalization
conjunction. RawRestrictedClassNormalization remains a dependency of the two separate
compatibility lemmas. No adopted source declaration is changed.

Removed the unused import `Sheaf.AlgebraicGeometry.QcoherentCohomologyComparisonPullback`:
coefficient naturality of the uniquely normalized comparison suffices for the scalar
calculation, and the raw restriction lemma uses the normalized pullback square directly.
Removed unused proof imports of `EtaleCohomologyPullbackFunctorial`,
`AbelianHigherDirectImagePresheaf` and module-presheaf sheafification from the item;
the action module retains its own required imports. Replaced the dense-subsite
SheafEquiv import by Basic. Consolidated duplicated public imports through the
extracted ComparisonData interface. No module is withdrawn. Every DAG parent and the proper-base-change unit route remain.
The earlier comparison-family citation remains in the unchanged mathematical statement
and its statement dependencies; only its direct proof use is pruned.
No declaration or public import in the adopted source library changes.

The following former direct edges remain required through ComparisonData:
`lem-pc-module-pullback-identity-composition`, `lem-pc-quasi-compact-base-change`,
`lem-sc-separated-over-affine-scheme-separated`,
`lem-weil-pbc-module-pullback-quasi-coherent`, and
`lem-weil-pbc-separated-base-change`.

The coefficient and higher-image interfaces remain required through ComparisonData,
CoherentHigherImageClasses and RawRestrictedClassNormalization:
`def-sc-etale-qcoherent-module`, `def-weil-pbc-abelian-etale-sheaves`,
`def-weil-pbc-etale-cohomology`, `def-weil-size-convention`, and
`sbc-lem-higher-direct-image-presheaf`.

The compatibility statements retain the former direct edges
`def-weil-pbc-cohomology-pullback`, `lem-pc-sites-module-sheafification-interface`,
`lem-weil-pbc-cohomology-pullback-functorial`,
`lem-weil-pbc-etale-base-change-finite-limits`, and
`lem-weil-pbc-etale-inverse-image-restriction`.
These transfers are not claims of globally pruned mathematics. The direct
`lem-weil-pbc-qcoherent-cohomology-comparison-pullback` family is unused by the new
proof, while its normalized pullback square remains needed for the raw restriction lemma.

Source counts above concern the packet's declarations. The delivery tool computes
any change in the targets' current Lean import closure against its pinned baseline.

## Where the brief, the DAG or earlier work was wrong

The written plan suppresses two actual interface calculations. The raw normalization
controls derived global-sections cohomology, whereas the coherent comparison uses Ext
cohomology transported by `sheafHDerivedEquiv`; its compatibility with chart restriction
and the tensor coefficient identification needs proof. Likewise the module-sheafification
interface requires a constructed scalar action on the full cohomology presheaf, including
non-affine objects. These are isolated with their precise statements and written proofs;
neither new statement is a renamed realization theorem.

## New nodes

`def-weil-pbc-affine-cohomology-comparison-data` owns the four unchanged definitions moved
from the item, with a public re-export, and the bundled interface to those same groups
and maps. Its evaluation and naturality API are proved. It introduces no new mathematical
choices.

`lem-weil-pbc-affine-cohomology-raw-restriction` isolates the fixed raw/normalized chart
restriction square, serving item steps 2 and 4.

`lem-weil-pbc-coherent-higher-image-module-action` isolates item step 3 independently of E.

The prior missing build artifact has been restored.
The final five-file packet passed `lcompile.py --all` on 2026-10-22: the classes,
comparison data, raw restriction, module action, and assigned module compiled in
31.2, 23.2, 3.8, 3.0, and 43.7 seconds respectively. Every file stayed below 60 seconds.
The original public theorem signature was also checked verbatim against the current source.
All diagnostic modules are outside the delivery's Lean tree.

The interface extraction is documented in
`coord/changes/affine-cohomology-comparison-data.md`.

The first final preflight requested LeanSearch records in addition to the recorded
LeanFinder/Loogle and source-grep searches, and a signature-only attachment for the
comparison-data node. Both records are corrected; these searches found no matching
Mathlib construction. The item's original statement dependencies are preserved.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
