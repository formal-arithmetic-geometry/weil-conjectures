## What changed

Replaced the hole in `AlgebraicGeometry.exists_smooth_functorial_ordinary_resolution`
with a complete assembly proof, keeping its statement and public import unchanged.
The proof obtains a synchronized embedded assignment, applies the existing
embedded-to-intrinsic reduction, realizes its local ordinary interface, constructs the
Zariski rule by restricting smooth comparisons to open immersions, applies synchronized
Zariski descent, packages its cover datum, and applies the existing smooth-comparison
descent theorem. The result is its `rule` field. The empty-input obligation for the
Zariski rule is proved by transporting the intrinsic tower's empty-input theorem through
the literal equality of labeled towers. A proved private helper converts the
isomorphic-source embedding predicate to the literal closed-immersion predicate.

The existing four reductions are all used, rather than re-stated. Added two conditional
interface lemmas in their own modules, with complete source-based proof plans and nodes.
Updated only this item's existing node's proof, proof dependencies, proof origin, and
obsolete tool approvals. No shared definition, existing statement, source-library
module, public import, attribute, or consumer is changed. No change record or forced
adaptation is needed.

Validation: the final remote `lcompile.py --all` run compiled all three files with
exit code 0 and no errors or warnings. `IntrinsicResolutionOrdinaryLocalRule` took
8.5 s, `SynchronizedResolutionDescentDatum` 7.9 s, and the item 9.4 s, all below 60 s.
The original theorem signature and public imports were checked unchanged, new node
signatures were checked against the Lean declarations, and all Lean lines are at most
100 characters. Every retained direct proof import is used.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_smooth_functorial_ordinary_resolution`
(node `lem-trf-smooth-functorial-ordinary-resolution`). Its module now contains zero
holes. Also proved private `descentEmbeddable_of_isEmbeddable`.

Added two holes, each a public theorem with body exactly `:= by sorry` in a new module:

- `AlgebraicGeometry.intrinsicResolution_ordinary_localRule`, node
  `lem-trf-intrinsic-ordinary-local-rule`, module
  `Sheaf.AlgebraicGeometry.IntrinsicResolutionOrdinaryLocalRule`.
- `AlgebraicGeometry.synchronizedResolution_descentDatum`, node
  `lem-trf-synchronized-resolution-descent-datum`, module
  `Sheaf.AlgebraicGeometry.SynchronizedResolutionDescentDatum`.

This is a decomposition: one hole closed, two added, net -1 before any import-closure
accounting. It is not a sorry-free proof of resolution. Existing conditional existence
theorems may still rest on their existing holes; this delivery does not change them.
No definition contains a hole, and no declaration is weakened.

The first new theorem only realizes the already supplied intrinsic assignment on the
embeddable domain as finite-index local comparisons, keeping its exact ordinary tower
and labels. It neither constructs global towers nor proves global coherence laws.
The second assumes fixed global towers and their synchronized Zariski descent, and
only constructs their cover datum with its count/map cocycle. It neither constructs a
resolution algorithm nor concludes global smooth comparisons. Both are strict parts of
the assembly, and the proof combining them with the four existing reductions is Lean.

## No longer needed

Removed these seven direct proof imports from the item:

- `WeilConjectures.Compactification.StrictTransformBlowup`
- `WeilConjectures.RingTheory.StandardSmoothQuotientLift`
- `Mathlib.RingTheory.Smooth.StandardSmoothCotangent`
- `Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties`
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `WeilConjectures.Blowup.FlatBaseChange`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber`

Their geometric arguments belong inside the existing conditional reductions, rather
than in this assembly. Every retained direct proof import is used by a named theorem
or by the two new conversion statements. None of the four declared proof dependencies
of the current assembly is bypassed:
`lem-trf-embedded-resolution-ambient-comparison`,
`lem-trf-embedded-to-intrinsic-smooth-resolution`,
`lem-trf-synchronized-resolution-zariski-descent`, and
`lem-trf-descended-resolution-smooth-comparisons` are all applied.

Removed the obsolete top-level `tool_uses` entries:
`lemma-nagata-strict-transform-ambient-closed`,
`lem-weil-pbc-smooth-locally-standard-smooth`,
`lem-weil-pbc-standard-smooth-quotient-lift`,
`lem-weil-pbc-standard-smooth-is-smooth`,
`thm-nagata-blowup-flat-base-change`, `lem-pc-smooth-flat`,
`lem-weil-pbc-smooth-ring-map-iff-smooth-affine`, and `lem-trf-smooth-composition`.
These were approvals for the old seven-step expanded argument; the current three-step
assembly uses the conditional reductions. Some are still dependencies of those
reductions, so this does not assert global unreachability of any of them.

No module is withdrawn. No existing dependency node is made globally unnecessary by
this delivery, and there is no claim that an upstream declaration can be removed.

## Where the brief, the DAG or earlier work was wrong

The existing DAG's mathematical assembly is sound, but its Lean interfaces do not
compose directly. The intrinsic reduction returns a lower-cut indexed assignment
with `IsFiniteTypeWithFiniteTypeKernels` coherence. Zariski descent consumes finite
ordinary comparisons with `RingedSpace.IsCoherent`. Smooth descent consumes another
local-rule interface and another affine-cover presentation, with a cover-comparison
cocycle in `Datum`. No existing conversion theorem was found after inspecting the
signatures and searching the project, Mathlib, and the blueprint. These are the two
new conversion steps; the existing four conditional reductions are not duplicated.

The item docstring retains the full original seven-step mathematical expansion. Its
Lean proof and updated node implement the current three-step conditional assembly,
with explicit finite-interface conversions. The new steps expand ILO VIII
2.1.4--2.1.9 and 2.3.4--2.3.5; they are marked agent expansions, not quotations of
separate theorems in ILO. The relevant source pages were read from the local PDF.

Checked the new statements on zero-length towers, empty inputs and empty covers,
identity maps, restrictions deleting every active center, finite disjoint unions, and
non-separated inputs. Count maps are between singleton index sets at length zero;
retained-center obligations are then empty. No affine intersection is assumed affine.
Comparisons keep proper centers even if their blowups are isomorphisms. The second
conversion fixes both its local rule and its global labeled towers, so its data are
not an arbitrary resolution chosen from an existence assertion.

The current unit `sk-i-curve-zero` is unchanged, including all its realization fields.
The item's recorded historical descent from `lem-trf-local-term-locality` is preserved
in the new nodes. This refines only this assigned descendant and bypasses no unit route.
There is no current rework or return entry requiring restoration of this existing item.

## New nodes

`lem-trf-intrinsic-ordinary-local-rule` realizes the supplied intrinsic assignment as
ordinary finite-index local comparisons, retaining the exact tower and labels.
Its proof converts the embedding predicates, transports coherence, enumerates retained
labels and counts source labels in target cuts, then transports the cartesian squares,
transition maps and center equations through the stage isomorphisms. The source is
ILO VIII 2.1.4--2.1.9, 2.3.4--2.3.5. LeanSearch, LeanFinder and source/blueprint greps
found no conversion theorem. Its declaration and full proof in words are in
`lean/Sheaf/AlgebraicGeometry/IntrinsicResolutionOrdinaryLocalRule.lean`.

`lem-trf-synchronized-resolution-descent-datum` converts the synchronized descent
of fixed global towers into the cover datum for smooth descent, for the same fixed
local rule. Enumerating a finite affine cover translates its presentation; the unique
full cover comparisons preserve every label, hence the local survivor embeddings and
counts are casts. Inductive uniqueness of ordinary blowup lifts gives the map cocycle.
The source is ILO VIII 2.3.4 and Remark 2.3.5(ii), with ordinary principalization and the
blowup universal property for the uniqueness argument. LeanSearch, LeanFinder and
source/blueprint greps found no matching constructor. Its declaration and proof in words
are in `lean/Sheaf/AlgebraicGeometry/SynchronizedResolutionDescentDatum.lean`.

## Second reading by H9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
