## What changed

Proved `AlgebraicGeometry.Scheme.root_cover_normalization_cartesian` with its existing
signature and public imports unchanged. Its two proof imports are now the newly proved
modules `NormalizationAffineLocalization` and `RootCoverGenericPullback`.

`Hom.isIso_normalizationPullback_affine_localization` adapts the already proved private
affine calculation from `NormalizationStalkBaseChange` into a public affine criterion.
It identifies qcqs sections under flat base change, applies the tensor-product
integral-closure localization theorem, and checks the canonical comparison map.

`root_cover_generic_pullback` explicitly constructs the pullback before normalization.
The DVR fraction field is localization at the uniformizer. The coefficient formula
identifies the preimage of the principal open. A cone lifts through the fraction-field
open immersion, then through hbranch and hT; those universal properties prove uniqueness.
The root-chart base-change square itself is unnecessary.

The main proof transfers hrootloc across the mapped-polynomial equality and both
GammaSpecIso ring equivalences, applies the affine normalization criterion, and constructs
a normalization isomorphism from normalizationDesc and normalization.hom_ext. It composes
that isomorphism with normalizationPullback and proves the requested square by
IsPullback.of_iso_pullback. No definitions or existing signatures were changed.

## Proved and sorry left

Closed one original hole: `AlgebraicGeometry.Scheme.root_cover_normalization_cartesian`
(node `lem-sbc-root-cover-normalization-cartesian`). No sorry remains in the item.

Both new public statements are proved, without sorry:
- `AlgebraicGeometry.Scheme.Hom.isIso_normalizationPullback_affine_localization`
  (`lem-sbc-normalization-affine-localization`).
- `AlgebraicGeometry.Scheme.root_cover_generic_pullback`
  (`lem-sbc-root-cover-generic-pullback`).

All private helpers are proved. Holes closed: 1; holes added: 0; split-off holes: 0.
The complete three-module set compiled cleanly through lcompile.py. The delivery dry run
performs the declaration/signature and axiom probes as well.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.Morphisms.NormalizationStalkBaseChange`
and the planned dependency `lem-sbc-normalization-stalk-base-change` from this item's
proof route. They may still be needed by other items. The direct flat-sections and
integral-closure-localization inputs remain needed and are recorded on the new affine
criterion node; their modules are provided through Mathlib.AlgebraicGeometry.Normalization.

The route no longer needs: identification of B with the stalk of Spec H; identification
of the root chart with a coefficient-stalk pullback; transport of normalization through
that stalk-chart identification; an AdjoinRoot coefficient-base-change pullback square.
No additional planned node named by the original proof_deps is omitted.

Removed redundant trial imports of Mathlib.AlgebraicGeometry.Morphisms.Flat and
WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat from the new affine module.
The new geometric module requires neither Mathlib.AlgebraicGeometry.Normalization nor
Mathlib.AlgebraicGeometry.Noetherian. All existing public imports of the item are retained.

## Where the brief, the DAG or earlier work was wrong

No false statement or broken tool was found. The planned stalk reduction is longer than
necessary: hrootloc already supplies the localization used by integral closure, and the
cover square can be proved from the basic-open coefficient formula without identifying
the whole root chart as a coefficient pullback. This replaces the below-unit route only;
the unit's realized list is empty and its spreading-cover steps are preserved.

Searches were actually run with msearch.py: LeanSearch was unavailable with HTTP 500;
LeanFinder found normalizationDesc/localization-diagram APIs but no exact public affine
comparison; Loogle found AdjoinRoot.map_of and the root-map API; the registered grep
searches had zero hits. Direct rg of the library found the private affine-localization
calculation and private DVR fraction-away proofs, which were read and adapted.
Blueprint searches for normalization localization, integral closure localization and
root cover had no matches; the broad localization search had no equivalent statement.

Edge cases: the affine criterion permits zero rings and empty schemes and does not
assume normality or finiteness. The geometric proof assumes the stated domain DVR and
irreducible uniformizer; it does not assume positivity of the exponent or a nonempty
cover, and its universal-property proof also works for empty root charts. All supplied
branch hypotheses are used to compare the whole cover, not one component.

## New nodes

`lem-sbc-normalization-affine-localization`, module
`Sheaf.AlgebraicGeometry.Morphisms.NormalizationAffineLocalization`: a fully proved
localization criterion, generalized from the existing private affine calculation. It
uses the existing flat-global-sections and integral-closure-localization nodes.

`lem-sbc-root-cover-generic-pullback`, module
`Sheaf.AlgebraicGeometry.Morphisms.RootCoverGenericPullback`: a fully proved cartesian
comparison of the covers before normalization. Its full cone construction is in Lean.
Both nodes inherit the item's chapter, unit and blueprint ancestor. No change record
or forced adaptation is needed.

## Second reading by V4

1. Interface preservation: PASS. Read all three delivered modules and diffed the
   existing module against the repository. The existing theorem signature and
   docstring are byte-for-byte unchanged; only private proof helpers, its proof,
   and two plain proof imports differ. No definition or public import changed.
   The existing node changes only proof, proof_deps and proof_origin. There are
   no forced adaptations or statement changes.
2. Proof validity: PASS. Compiled all three modules in import order through
   lcompile.py with no errors or warnings. Independently compiled a temporary
   import probe with #print axioms for all three public theorems: each uses
   exactly propext, Classical.choice and Quot.sound, with no sorryAx. Scanned
   every delivered Lean file: no sorry, axiom, unsafe, opaque, implemented_by,
   extern or hollow definition. All lines meet the 100-character limit. The
   temporary probe was removed before delivery.
3. New statements: PASS. Both new statements are fully proved and strictly
   separate parts of the argument, not renamed unproved copies of the item.
   The affine criterion is valid also for zero section rings and empty source
   schemes: the qcqs flat-sections and integral-closure localization theorems
   have no domain hypothesis. The generic model proof makes no positivity or
   nonemptiness assumption on the root chart; the uniformizer hypothesis
   supplies the only domain-dependent step. Its cone construction lifts through
   the principal open and then hbranch and hT; its uniqueness uses their actual
   universal properties. Classical choice here selects lifts from proved
   existence, not data from an unproved theorem. Independently searched with
   LeanFinder for relative integral closure under multiplicative localization,
   Loogle for IsLocalization.Away and FractionRing, and registered grep for
   normalizationPullback and associated_pow_irreducible. Read the matching
   Mathlib normalization/localization APIs and repository private calculations;
   no public theorem replaces either new statement with this interface.
4. Route and pruning: PASS. The main theorem transports the supplied
   localization to global sections, applies the affine criterion, and transports
   normalization along the proved generic pullback. No extra geometric
   hypothesis is introduced. The sole old proof dependency was
   lem-sbc-normalization-stalk-base-change; it and its plain import are both
   listed under No longer needed. The new modules have only imports required
   by their statements or underlying proof APIs. Read
   dag/units/sk-prop-input-spreading.json: its realized statement and all seven
   step lists are empty, and the spreading-cover unit route is unchanged.
5. DAG agreement: PASS. Checked the three nodes against the Lean declarations
   and proof bodies. The affine node names the qcqs flat-sections and
   integral-closure-localization inputs; the generic node records the DVR
   principal-open identification and full cone argument; the item uses exactly
   these two nodes and the normalization universal property. New nodes have
   source, proof, proof_origin, search records, created, blueprint, chapter, unit
   and verbatim Lean signatures as required. No additional old dependency was
   silently dropped.

Second reading changed only this report: added the independent checks and
verdicts. No proof repair was needed. Original holes closed: 1; holes added: 0;
split-off holes: 0. Both added public lemmas are proved.
