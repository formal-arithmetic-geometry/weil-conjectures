## What changed

Repair of returned head `870ff0b861f` (reviewer C-870ff): the mathematical
review passed, but the merge rejected the reviewer's bare fix filename
`ringed-projection-restriction-data.md`. The stage-3 merge tool maps that
record to the fix alias `ringed-projection-restriction-data.change.md`
(`tools/batch_land.py`, function `fixes`). The delivery itself contains the
record at `coord/changes/ringed-projection-restriction-data.md`; no duplicate
record or launcher/tool modification is needed.

Refreshed that record against the current sheaf-dag source graph, covering
1,898 current consumers and packet modules, plus 684 recorded planned
DAG consumers, with current holders. Confirmed that the
entire moved exposed data block is identical to current main (32,497
characters). The original assembly signature is preserved, and the retained
packet contains the same seven Lean modules and two named holes. The delivery
tool rebases on current sheaf-dag and performs server compilation and preflight
before pushing. For a reviewer correction of the record, use the documented
`ringed-projection-restriction-data.change.md` fix alias.

Separated the unchanged normalized interfaces into
`Sheaf.Paper.RingedProjectionRestrictionData`, publicly re-exported by the original module.
This permits the global and localized construction lemmas to be imported without a cycle.
Every original data declaration, instance, universe, visibility and body is unchanged;
the entire exposed declaration block was checked byte for byte. The theorem signature is
unchanged. No target or source-library declaration changed.

Proved `SheafOfModules.ringedRestrictionLocalIso` for independent site-object, site-arrow,
coefficient and localization universes. The proof constructs a covering family from the
covering sieves, transfers isomorphisms through the exact-derived cohomology comparison,
uses sheaf gluing, reflects isomorphisms to modules and applies derived cohomology detection.

The global construction explicitly builds the module operation, transfers exactness by
adjoint uniqueness, proves derived-counit normalization and shift compatibility, builds
the tensor models from the existing resolving descent, and transports the ordinary
pure-unit tensor comparison. The tensor comparison is now constructed by pure-tensor naturality, totalization
and fully faithful descent; its remaining input is only the separate signed shift
compatibility lemma. The assembly constructs the global and localized
witnesses and applies the proved local criterion. The two remaining results have complete
natural-language proofs and separate DAG nodes.

## Proved and sorry left

Closed the original body hole in
`AlgebraicGeometry.Scheme.ringedProjectionRestriction` (1 original hole closed).
Its combination proof compiles without a hole.

Proved the new theorem `SheafOfModules.ringedRestrictionLocalIso` with no holes, node
`lem-weil-pbc-ringed-restriction-local-iso`.

Added two holes, each exactly `:= by sorry` in its own module:

- `AlgebraicGeometry.Scheme.ProjectionRestriction.tensorComparison_shifts`, node
  `lem-weil-pbc-ringed-projection-tensor-shifts`: the two signed shift squares for an
  already constructed, representative-normalized comparison, on arbitrary ringed sites.
- `AlgebraicGeometry.Scheme.ProjectionRestriction.localModel_exists`, node
  `lem-weil-pbc-ringed-projection-local-model`: localization of a supplied global package
  and compatibility of its projection mate.

The retained intermediate hole in
`AlgebraicGeometry.Scheme.ProjectionRestriction.globalTensorComparison_exists` was also
closed in the retained delivery. Its proof establishes ordinary naturality by pure-tensor
extensionality, preserves resolving complexes by adjoint uniqueness and isomorphism
transport, and descends the total comparison via `tensorComparisonDescent`. All three
private helpers have complete proofs. Only shift compatibility is imported from the
new shifts lemma; this is a proper part of the former existence statement.

The new `AlgebraicGeometry.Scheme.ProjectionRestriction.globalModel_exists` is proved
from the existing construction declarations and the new tensor comparison result. Its
private adjunction, tensor model and ordinary tensor helpers contain no holes.

Thus the original module has 0 holes; the packet adds 2. This is 1 decomposition and a
proved local-detection component; it is not a net hole reduction. Existing holed dependency
theorems are used under the stage-3 policy. No data is defined by choosing an arbitrary
witness of an unproved existence theorem.

Current return-repair validation (2026-10-22, returned head `870ff0b861f`):
all seven submitted modules passed `lcompile.py --all` on the server, exit 0
and no warnings. Data, local criterion, local model, tensor shifts and tensor
comparison reused accepted server artifacts (0.0–0.1 s each); global model
compiled in 30.7 s and assembly in 2.6 s. No full-library build was run.

Earlier validation: the original six-module packet compiled in import order through lcompile.py:
Data 26.1 s, local criterion 9.8 s, local statement 2.2 s, tensor statement 2.5 s,
global construction 28.5 s and assembly 2.4 s. A subsequent import cleanup makes the
cohomology-sequence import private; delivery preflight verifies that final version.
Current tensor validation: the revised `RingedProjectionTensorComparison` compiled
through lcompile.py in 29.2 s, with no warnings and no local holes. Its new shift
statement compiled in 2.0 s. The subsequent saved-artifact consumer compile passed
in import order: tensor comparison 44.8 s, global construction 51.3 s, assembly 5.5 s,
all without warnings. Data, local detection, the local statement and the new shift
statement had already passed unchanged in the earlier phase of this session. No full-library build was run by this worker.

## No longer needed

Removed these 27 unused private imports from the data/assembly layer:

- `Sheaf.Paper.LocalizeRingedSiteMorphism`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `WeilConjectures.CategoryTheory.LocalizedModuleAdjunctionExact`
- `Mathlib.Algebra.Category.Grp.FilteredColimits`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`
- `Mathlib.Algebra.Category.Ring.Limits`
- `Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck`
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`
- `Mathlib.Algebra.Category.Grp.AB`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits`
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`
- `WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`
- `Sheaf.Paper.RingedExchangeTensorCoherence`
- `Sheaf.Paper.ProjectionMateExact`
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Sheaf.Paper.LocalizeRingedSiteMorphismGeneral`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`

The original six public imports are retained through the public Data import. The two
private imports still used by the definitions are retained. No declaration or module is
withdrawn, and no blueprint unit route is bypassed. The generic slice and tensor
construction dependencies remain in the construction nodes; removing their unused direct
imports here does not assert that their mathematics is unnecessary. The assembly no
longer directly applies `def-weil-pbc-adjunction-mate`,
`lem-weil-pbc-ringed-projection-mate-exact`, or
`lem-weil-pbc-localization-universal-property`: the construction lemmas now own the
localization and mate arguments. The final detection proof needs no fraction argument:
Mathlib's derived cohomology criterion applies directly. No parent module is withdrawn.

The tensor-comparison route no longer directly uses
`lem-weil-pbc-slice-tensor-integer-shift-compatibility` or
`lem-weil-pbc-derived-tensor-shift-descent`: it constructs the total comparison and
uses only the remaining signed-shift result. These nodes still support the global
model's tensor-shift construction, so neither module is proposed for withdrawal.

## Where the brief, the DAG or earlier work was wrong

The first retry of head `870ff0b861f` passed compilation and axiom checks,
but preflight found the newly landed consumer
`Sheaf.Paper.NormalizedCompletedOperationModels` outside the earlier inventory.
It imports the operation interfaces transitively; its textual `tensor` and
`Operation.pullback` matches remain valid through the identical public data
re-export. Refreshed the source import closure and added recorded planned DAG
consumers conservatively. No Lean source adaptation or new hole is needed.
Nothing was pushed on this failed preflight.


The first submission of this return repair passed compilation and reached server
preflight, which found one additional consumer that had landed after the initial
inventory: `Sheaf.Paper.QcqsProperSerreHeartBound`. Its `Mod` match is the independent
`AlgebraicGeometry.ProEtale.CondensedRing` module-object notation. The unchanged
ProjectionRestriction re-export preserves the imported interface. Added its current
consumer entry and refreshed the full inventory; no consumer source adaptation is
required. No push occurred on that failed attempt.


The generic small-site slice interfaces use equal object and morphism universes and
coefficients in that universe. The pro-etale interfaces in this item have objects in
u+1 and arrows in u, so the suggested direct specialization does not elaborate without
additional transport or an independent-universe construction. The existing independent-
universe restriction and cohomology APIs do apply, and prove the final clause directly.
The source statements are not disputed.

The data and theorem originally occupied one module, preventing independent construction
modules from importing the data while the assembly imports their results. The declaration
move resolves that import cycle without changing any mathematical definition. The change
record lists all direct importers and namespace users; no consumer needs adaptation.

The server repeatedly returned exit 124 with no answer between successful compiles. Those
requests were retried; they were not classified as Lean timeouts or as a proof obstruction.

Resumed validation (2026-10-22): compared the moved data block with the current
library source byte for byte; all declarations and bodies remain identical. Confirmed
zero holes in Data, the global construction, local detection and assembly. This
session additionally proved ordinary tensor naturality and resolving preservation,
and replaced the tensor-comparison hole by the strictly smaller signed-shifts result. The previous
attempt's consumer-inventory and parser-signature repairs are retained. The earlier
exit-143 delivery attempts did not push. The first resumed delivery was refused by
the early split policy (37 of 120 reference minutes); no branch was pushed. Work
continued on the retained tensor result. The revised seven-module packet compiled
through lcompile.py in the phases recorded above. The next delivery completed its
module compilation and reached server preflight, which found additional consumer
modules that had landed while checks ran. Added those 79 module entries to the
change record; the Lean packet was unchanged. Three axiom probes returned the
server-busy timeout; the delivery tool defers these probes to the merge.

Further scratch work proved both total-complex shift squares and both arguments
extending shift equalities from resolving pairs to arbitrary derived objects,
without holes or warnings. These calculations and proof notes are retained outside
the submitted lean/ tree; the submitted packet still has precisely the two holes
listed above. The next retry passed the consumer check and all module compilation. Preflight
then reported one remaining metadata issue: the new tensor-shifts node lacked
LeanSearch and LeanFinder records. Ran LeanSearch, LeanFinder and Mathlib source
grep for that precise statement; recorded all three results and verdicts. They
supply the canonical derived-factor shift instance and general shift machinery,
without matching the complete arbitrary-model tensor comparison theorem.

The additional scratch calculations now also prove the exact-derived factors
shift identity, both normalized representative equations with the final inverse
cancelled, and invertibility of the comparison normalization tail. Together with
the four earlier calculations, eight component results compile without holes or
warnings outside the submitted lean/ tree. The submitted packet still adds only
the same two named holes. Delivery is being rerun with the complete search metadata
and current consumer inventory.

Repair of landing failure (2026-10-22): the old inventory had become stale
while new consumers landed. Regenerated it from the current source import
graph, including every transitive importer and all packet modules. Explicitly
covered CoefficientExtensionReductionData, CoefficientExtensionRepresentativeRoos,
CoefficientExtensionStrictRepresentatives, CompactSupportCoefficientTransition
and CompletedOpenKFlat. Their referenced Mod, derived, Restriction.model,
Operation.pushforward and Operation.left declarations retain identical bodies
and remain publicly available through the data re-export, so no forced
consumer adaptation is necessary. No new holes were added by this return repair.

## New nodes

`def-weil-pbc-ringed-projection-restriction-data` owns the unchanged normalized tensor,
restriction and comparison interfaces in Data. The existing operation-definition node
`def-pur-ringed-module-derived-operations` now points to Data with its statement unchanged.

`lem-weil-pbc-ringed-restriction-local-iso` records the proved independent-universe
cohomology-and-gluing criterion. Its empty-site and empty-cover cases use precisely the
ordinary Grothendieck-topology covering axiom; no nonempty-cover assumption is added.

`lem-weil-pbc-ringed-projection-global-model` isolates global operations and tensor
normalizations and is proved from the existing interfaces and the separate tensor result.

`lem-weil-pbc-ringed-projection-local-model` isolates one localized square from an already
supplied global package. It assumes that package and has no cover-local detection clause.
Its source argument is retained in its docstring and node proof steps.

`lem-weil-pbc-ringed-projection-tensor-comparison` isolates the canonical derived tensor
comparison, after operations, ordinary tensor comparison, models and shifts have already
been supplied. It constructs neither operations nor localization. This theorem now has a complete
proof from the listed construction results and the separate signed-shifts lemma.

`lem-weil-pbc-ringed-projection-tensor-shifts` isolates just the compatibility of an
already supplied normalized comparison with the prescribed shifts. It constructs
neither the comparison nor its preservation or representative fields. Its zero-shift,
zero-ring and empty-site cases introduce no extra assumption. Thus it is strictly a
part of the tensor comparison argument, not the original existence theorem renamed.

Change record: `coord/changes/ringed-projection-restriction-data.md`.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
