## What changed

Replaced the proof of
`WeilConjectures.CompletedCoefficientPushforward.directImageDiagrams_exists`
without changing its signature or the existing models. The proof constructs the
normalized right image on completed-module towers, the evaluation squares, the
ordinary inverse-limit comparison, and the normalized derived-limit comparison.
It proves the projection equation by the universal property of the composite
right derived functor: after the unit and the exact evaluation factors, the
calculation is the ordinary equation for `limit.post` and a limit projection.

The proof reuses the existing generic helpers in
`RingedStrictTowerHomotopyLimitIndependentCoefficients`,
`RingedTowerPushforwardLimitComparison`, and
`DiagramRingRestrictionPushforward` through proof-only `import all` imports.
It adds three proof-only imports for the remaining subarguments. No existing
module besides the item is changed, and no public import is removed.

The three new modules isolate coefficient comparisons, strict-system comparisons,
and inverse-limit acyclicity. `StrictImageData` is an actual record containing
only the system fields, parameterized by the already fixed coefficient and tower
images. `completedPushAdditive` proves additivity of the actual sectionwise
completed-module pushforward; its data contains no hole.

Validation: all four modules compiled with no diagnostics through `lcompile.py --all`.
The item took 46.2 seconds; the three new modules took 6.7, 6.2 and 5.0 seconds.
The final edits after that run change docstrings and DAG/report text only.
The first delivery preflight found one metadata error: the new structure node
recorded fields in `lean.statement`. Its record now contains the declaration
signature, as required; the structure and all Lean statements are unchanged.

## Proved and sorry left

The existing hole in `directImageDiagrams_exists`
(node `lem-pur-completed-coefficient-direct-image-diagrams`) is closed from three
strictly smaller new statements. This is a decomposition: one existing hole
closed, three added, net minus two holes, not an unconditional proof of the
mathematical assertion. There is no `sorry` left in the item module, including its
private helpers.

Every new hole is a whole named public theorem in its own module:

- `WeilConjectures.CompletedCoefficientPushforward.coefficientComparisons_exists`
  (`lem-pur-completed-coefficient-image-comparisons`): only constant, finite and
  quotient coefficient squares and their coherence; no system or limit data.
- `WeilConjectures.CompletedCoefficientPushforward.strictImage_exists`
  (`lem-pur-completed-coefficient-strict-image`): only the system direct image and
  its square for a supplied coefficient package and a supplied tower image; no
  tower evaluation squares or inverse-limit data.
- `WeilConjectures.CompletedCoefficientPushforward.towerLimit_push_acyclic`
  (`lem-pur-completed-coefficient-tower-limit-acyclic`): invertibility of the target
  limit unit on the levelwise pushforward of a K-injective tower. This has no
  coefficient, system, composite-comparison or projection conclusions.

The combining proof constructs the tower image and evaluation comparisons and
proves the limit projection equation; none of these is another new hole.

## No longer needed

No original import was removed, and no existing module is withdrawn.

The direct-image-diagrams proof no longer needs
`lem-pur-completed-coefficient-structure-map`: its map and compatibility equations
are supplied in the theorem hypotheses. It also does not use
`lem-weil-pbc-profinite-coefficient-inverse-image`: no inverse-image comparison of
the completed coefficient ring is needed. The fixed-constant-module presentation
of `lem-weil-proetale-direct-image-restriction-of-scalars` is replaced by the
ringed-topos coefficient-square argument on the actual ring sheaves. These are
removed from the item's proof dependencies, with no claim that other consumers
or the model imports cease to need their modules.

The old direct dependencies on completed-coefficient definitions, coefficient
system derived comparison, ringed composition and its cocycle, and K-injective
total derivation now occur in the appropriate smaller subarguments or in the
existing generic construction helpers. The item DAG records its actual new
proof dependencies. No blueprint unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The plan's mathematical argument is valid, but its declarations are not directly
applicable by specialization on the original sites: several general ringed-topos
theorems require small sites whose object, morphism and coefficient universes
coincide. The item retains a site with object universe t+1, morphism universe t,
and independent coefficient universe max u (t+1). The remaining lemmas explicitly
include transport from equivalent small sites and normalization against the
supplied exact or universal units. None asserts that restriction of scalars
preserves K-injectivity. The tower evaluation step does preserve K-injectivity,
and uses the existing theorem for that fact.

Removed the inherited options disabling backward transparency checks. The proof
uses the default checks and a proof-only `import all` of
`Mathlib.CategoryTheory.Limits.HasLimits` to expose the chosen-limit construction
for definitional equalities. The completion statement and all target statements
are unchanged.

## New nodes

`lem-pur-completed-coefficient-image-comparisons` isolates the coefficient part of
original step 2, following Stacks Tag 0D6E and the normalized cocycle/unit laws.
Its edge cases include identity quotient maps and empty sites.

`def-pur-completed-coefficient-strict-image-data` records only the system fields of
the old full comparison. It has concrete record data, no choice from an unproved
existence theorem, and no limits. `lem-pur-completed-coefficient-strict-image`
constructs this system part, following the diagram-site use of Tag 0D6E and Zheng
Construction 4.1. It applies to arbitrary strict systems and retains their
transitions and maps before evaluation.

`lem-pur-completed-coefficient-tower-limit-acyclic` isolates the acyclicity input
of original step 4, following the first proof of Stacks Tag 0A07 and Tag 0D6E.
The ring map need not be flat or invertible. Naturality of any supplied universal
limit unit transports the K-injective calculation to that model. Zero complexes,
identity maps and empty sites are included.

Searches used LeanSearch, LeanFinder, Loogle, the remote Mathlib grep, and local
searches of both library roots. The generic helpers were reused. Loogle did not
recognize the requested identifier and is recorded as unavailable, not as a
mathematical nonexistence result. No change record is needed for an existing
shared interface: none is changed.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
