## What changed

Replaced the proof of `AlgebraicGeometry.zariski_prelog_logification_comparison` by an explicit
construction and assembly, preserving its entire signature and all thirteen properties.
The proof obtains the Zariski data, constructs the two normalized inverse images, constructs
both étale logifications and their universal properties, and combines the remaining geometry.

Two new construction theorems have complete proofs:

- `AlgebraicGeometry.prelog_etale_inverse_image_construction` sheafifies the prescribed
  open-image diagram, constructs its natural structural map using scheme pullback identities,
  extends it by `sheafifyLift`, and proves the exact unit equation and Hom bijection.
  A private, proved filtered-colimit instance supplies the concrete sheafification instances
  on a small model of the affine étale site; dense-site equivalence transports them back.
- `AlgebraicGeometry.prelog_logification_etale_construction` uses the existing
  `prelog_pushout_log_axiom` and `prelog_pushout_hom_extension`. A proved quotient-kernel
  isomorphism transfers the actual pair maps and proves their naturality, structural formula,
  inclusion formula, and sheafification universal property. The unique extension is then
  bundled with its structural equality, including uniqueness in the required subtype.

The remaining geometric arguments are isolated into two public statements in separate new
modules: a purely Zariski construction with characteristic geometry, and an étale comparison
and stalk result taking all three logifications and their universal properties as inputs.
Each has a complete source-based proof in its docstring and a matching DAG node. These are
strict parts of the argument; neither restates the original theorem or assumes its conclusion.

Moved the original seventeen definitions, with their names, universes, signatures, and bodies
unchanged, to `PrelogLogificationData.lean`. The item publicly re-exports them. This lets the
new statements use the actual existing predicates without a circular import. The unnecessary
old file-level transparency relaxations are removed. The change record is
`coord/changes/prelog-logification-data-relocation.md`.

Repair of returned head `511754fafaa`: changed exactly one import in the existing
`PrelogUnitPushoutPresentation` module, from a public import of
`ZariskiPrelogLogificationComparison` to a public import of `PrelogLogificationData`.
All declarations, signatures, definition bodies, proofs and visibility in that module are
byte-for-byte unchanged. The presentation consumes the relocated definitions, not the
comparison theorem. This removes the back edge responsible for the returned import cycle.
No other existing Lean module besides the assigned item and this presentation is changed.

Compared the retained packet against the current shared sources. The current
`PrelogPushoutLogAxiom` now uses `PrelogUnitPushoutPresentation` and has a complete proof;
the repaired import graph, including those current sources, has no cycle in the item's
415-module import closure. All seven delivered modules and both direct importers of the
adapted presentation compiled
against the repaired sources (2.7--9.5 seconds per file), in one import-ordered run.
`PrelogPushoutLogAxiom` compiled in 9.5 seconds and `EtaleLogPresentationComparison` in
7.5 seconds. Their temporary unchanged copies were removed after the successful check.
The import adaptation is recorded in
`coord/changes/prelog-unit-pushout-data-import.md`.

## Proved and sorry left

The item originally had one hole, in
`AlgebraicGeometry.zariski_prelog_logification_comparison`; that declaration now has a complete
Lean proof from named dependencies, and its module has zero holes.

Added exactly two holes:

- `AlgebraicGeometry.zariski_prelog_logification_geometry`, node
  `lem-trf-zariski-prelog-logification-geometry` in `ZariskiPrelogLogificationGeometry.lean`.
- `AlgebraicGeometry.prelog_logification_etale_geometry`, node
  `lem-trf-prelog-logification-etale-geometry` in `PrelogLogificationEtaleGeometry.lean`.

The new data, inverse-image construction, and étale construction modules have no holes.
In particular, there is no hole in any definition or private helper.
The current pushout and hom-extension dependencies are already proved. Their current
statements are used as the brief prescribes; their sources are not changed by this delivery.

This is a decomposition: one original hole closed and two strictly smaller geometric holes
added, for a net increase of one hole in these delivered declarations. It is not counted as a
complete proof of the full logarithmic result. The two fully proved construction steps and the
formal assembly are real Lean work beyond moving the hole.

## No longer needed

The item now needs only its public data import and four proof imports, each actually used.
The additional repair removes `PrelogUnitPushoutPresentation`'s public import of the consuming
comparison module, replacing it with the exact data module it uses. Neither mathematical
module is withdrawn; no new pruning claim is made.
The two necessary old public imports, `ZariskiLogStructure` and `Mathlib.CategoryTheory.Sites.Over`,
move to the data module. Removed the unused public imports
`Sheaf.CategoryTheory.Sites.GeometricMorphism` and
`Mathlib.CategoryTheory.Sites.PreservesSheafification` from this interface.
`MonoidChartCharacteristicFan` already imports `GeometricMorphism` explicitly.

Removed these six old private imports from the item:

- `WeilConjectures.AlgebraicGeometry.ZariskiEtaleInclusionMorphismOfSites`;
- `WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`;
- `Mathlib.CategoryTheory.Functor.Flat`;
- `Mathlib.CategoryTheory.Limits.Types.Filtered`;
- `Mathlib.CategoryTheory.Sites.Point.Skyscraper`;
- `Mathlib.CategoryTheory.Sites.CoverLifting`.

The generic change-of-site, local sheafification, filtered pushout, geometric stalk, basic-open,
and slice-comparison dependencies remain in the plans of the two new geometric statements.
The original node's proof dependencies now name exactly the four construction/geometry steps
used by its proof. No old mathematical node or existing module is withdrawn, and no unit
statement or realized unit step is bypassed. No globally unused old module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement is unchanged and no false lemma was found. The original module
combined presentation definitions with their large consuming theorem; importing new statements
using those definitions would create a cycle. The definition-only extraction resolves this
without changing the actual notions. The returned packet missed the additional back edge
through the now-proved `PrelogPushoutLogAxiom` and its presentation import. Single-file
compiles against published artifacts did not detect that source import cycle. This repair
redirects the presentation to the extracted data module and checks the overlaid source graph
as well as compiling both direct consumers. The maintainer's reported cycle is repaired by
that import change, not by replacing any proved result or deleting a declaration.

The small étale `HasSheafify` instance could not be inferred directly for `CommMonCat` because
Mathlib supplies its explicit filtered-colimit cocones but not the all-colimits instance used
by the convenient site instance. The construction proof supplies just the needed filtered
colimits privately, obtains concrete sheafification on the small affine model, and transports
it by the existing dense-site equivalence. No universe is enlarged in any public signature.

Checked the local ILO source at VI 1.1 (p.69), VIII opening of §3 (p.97), and VIII 3.3.2
(p.106). The arbitrary-prelog expansion remains explicitly agent-written, as in the assigned
node, rather than being attributed verbatim to the chart-specific source statement.
Edge cases checked for the two new geometric statements: empty scheme and empty étale object,
unit-valued prelog map, trivial monoid, and arbitrary noncancellative monoids. Their formulas
and arguments use no nonemptiness, finite generation, cancellation, or injective transitions.

The unit record `sk-i-curve-zero` and its current blueprint text were read. Its realized
statement/step arrays are empty; this delivery retains the assigned historical logarithmic
auxiliary and changes neither the unit nor its route.

## New nodes

`def-trf-prelog-logification-data`: owns the seventeen relocated definitions and predicates.
There are no new mathematical notions, no definition holes, and no changed signatures.

`lem-trf-prelog-etale-inverse-image-construction`: fully proved construction of the normalized
inverse image; applies to every scheme, without Noetherianity.

`lem-trf-prelog-logification-etale-construction`: fully proved normalized étale presentation
and log universal property from the two existing assigned dependencies.

`lem-trf-zariski-prelog-logification-geometry`: the remaining Zariski half, with its
characteristic quotient, normalized stalks, universality and restrictions; one named hole.

`lem-trf-prelog-logification-etale-geometry`: the remaining comparison, étale and characteristic
stalks, and étale slice restrictions for already supplied universal logifications; one named hole.

All new nodes are in the item's chapter and unit, carry the recorded Mathlib searches,
source, explicit proof steps, and exact Lean attachments. The main node records the actual
assembly route. Change records: `coord/changes/prelog-logification-data-relocation.md` and
`coord/changes/prelog-unit-pushout-data-import.md`.

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
