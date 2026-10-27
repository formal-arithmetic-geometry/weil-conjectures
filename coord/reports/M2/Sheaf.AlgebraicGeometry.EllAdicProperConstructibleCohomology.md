## What changed

Filled `properLowerStar_constructible_cohomology_ellAdic` in the assigned module,
with its signature and four public imports preserved. All added helpers are private
and proved. The returned duplicate helpers are removed: the proof privately imports
`Sheaf.AlgebraicGeometry.FiniteProperClassicalCoproducts` and
`Sheaf.Paper.LocalizingClosureCtfEqualsBc` with `import all`, then directly uses
`AlgebraicGeometry.ProEtale.etale_cd` and
`AlgebraicGeometry.ProEtale.ordinary_constructible_iff`. The proof first establishes
finite-field proper finiteness using the identity compactification, finite fibre
dimension, and the étale/pro-étale comparison.
It transports this to internal finite coefficients and applies the existing integral
residue and direct-image-limits criteria. Explicit continuous ring isomorphisms
identify the integral coefficient presentations. Integral models and exact scalar
extension handle finite rational coefficients, and finite-field descent handles the
condensed algebraic closure. The four coefficient constructors are covered.

Updated the item's existing DAG proof, proof dependencies and proof origin to this
route. No statement, definition used by a target, source-library file, or public
import was changed. No new public declaration or module was added.

## Proved and sorry left

Hole closed (1 of 1):
`AlgebraicGeometry.ProEtale.CondensedRing.properLowerStar_constructible_cohomology_ellAdic`
(`lem-sfb-noetherian-proper-constructible-cohomology`). Holes added: 0. Holes left
in the item: 0. Split off: 0. Existing declared dependencies with unfinished proofs
are used as stage-3 inputs; their proofs are not claimed by this delivery.

The repaired module compiled with `lcompile.py`: exit 0 in 25.8 seconds, with no
compiler warnings or errors. The original public theorem signature and all four
public imports were checked byte-for-byte against current shared source. All Lean
lines are at most 100 characters. Delivery preflight supplies the consumer and
independent-reader checks. No second-reader claim is made here.

## No longer needed

The item's route does not use the separate good-truncation/Serre dévissage step:
`def-kun-truncations`, `lem-weil-pbc-condensed-constructible-serre`, and
`lem-weil-pbc-integral-constructible-serre` are removed from this node's proof
requirements. The finite-coefficient and integral criteria already accept bounded
complexes. Their modules and all upstream declarations are retained in the library;
this is pruning of this proof's requirements, not a claim of global withdrawal.

The general continuity dependency
`lem-weil-pbc-condensed-qcqs-pushforward-continuity` is replaced as a direct input
by the established integral and finite-subfield scalar/direct-image comparison
statements. Continuity remains needed where those statements use it.

Removed the unused retained proof import
`Sheaf.Paper.FiniteLocalizingExceptionalPreservation`; that quarantined module is
neither restored nor withdrawn. The exceptional-localization branch is not needed.
The returned packet's local duplicates `CondensedRing.finiteEtale_cd` and
`CondensedRing.ordinary_constructible_iff` are deleted, together with their now-unused
private `cover_exists_iff` helper. The existing private library lemmas supply these
facts directly; their modules remain imported and are not pruned.

Removed the now-redundant direct proof imports
`Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound`,
`WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison`,
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle`, and
`WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations`. They are needed
inside the reused cohomological-dimension helper, whose proof is retained unchanged.
The corresponding DAG dependencies therefore remain recorded for that input.
Also removed the unused retained direct imports
`Sheaf.Paper.CondensedCoefficientIsoConstructible` and
`Sheaf.UpstreamExtra.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`;
their needed public interfaces remain available through imports actually used.
No module is deleted.

The original source also directly imported the four planned proof inputs
`Sheaf.AlgebraicGeometry.CondensedConstructibleSerre`,
`Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`,
`Sheaf.Paper.CondensedQcqsPushforwardContinuity`, and
`Sheaf.Paper.IntegralConstructibleSerre`; those direct imports are removed.

## Where the brief, the DAG or earlier work was wrong

The original integral proof step had an empty `uses` list despite requiring proper
finite-coefficient finiteness, a residue/direct-image comparison, and a completeness
criterion. These are now explicit declared dependencies. The existing integral
proper theorem over separated finite-type schemes over a positive-characteristic
field does not apply to this item's arbitrary Noetherian base. The proof uses no such
extra geometric hypothesis and covers zero objects and empty schemes through the
general input statements.

The earlier missing Mathlib artifacts recovered. Subsequent failures were proof
elaboration/performance diagnostics, not an infrastructure blocker. The initial
retained-packet delivery run pushed nothing: it refused the quarantined missing
proof import, which has now been removed. No launcher, budget metadata or shared
source was modified.

The launcher resumed this packet after pausing it to reduce the compile queue.
The reference metadata changed from start `1792742442.6473992` to
`1792774064.5653317` during that pause/resume; the worker did not edit it.

Preflight requested a change record because the proof adds `open ZeroObject` and
local irreducibility attributes. Added
`coord/changes/M2-elladic-proper-proof-controls.md`, with the old/new command blocks
and all nine downstream modules. The attributes are local, and no consumer or
mathematical interface changes. No forced adaptation is needed.

Return at head `c7581c10e`: both reported word-for-word duplicates were genuine.
The repair removes both declarations and calls the existing library lemmas directly,
instead of reproducing their proofs. Their signatures were checked, including
coefficient universes and the compact/quasi-separated scheme instances. Both new
private imports pass `tools/import_direction.py may`. The retained DAG is rebased
onto current source, preserving all current metadata except the owned proof fields.
No new node or hole is introduced by this repair.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
