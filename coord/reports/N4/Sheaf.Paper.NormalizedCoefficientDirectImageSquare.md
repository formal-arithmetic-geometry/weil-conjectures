## What changed

Filled `AlgebraicGeometry.Scheme.normalizedCoefficientDirectImageSquare` using the
existing, proved `CategoryTheory.ExactDerivedSquare.normalized_cube`, accessed by a
proof-only `import all Sheaf.CategoryTheory.DerivedExactSquareCoherence`.
The ordinary cube is proved sectionwise in the new module
`Sheaf.Paper.CoefficientDirectImageRestrictionCube`. The derived identity restriction
unit law is proved in `Sheaf.Paper.ExactRestrictionDerivedIdentityUnit`.
These are proof steps of the original argument, with complete proofs and matching
new nodes. The item imports them only for its proof. Existing definitions, public
imports, theorem signatures and consumers retain their interfaces.

After replacing broad section rewrites with an explicit section equation, local
irreducibility prevents unfolding chosen derived functors and coefficient comparisons.
Profiling exposed remaining costs of unfolding the localization constructions.
The completed ordinary and unit calculations were then moved into their own modules,
as permitted by steps 3a and 5 of the current dispatcher brief. No transparency
respect option or server wall-time limit is changed. Debug profiling options are removed.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Scheme.normalizedCoefficientDirectImageSquare`
(`lem-pbc-normalized-coefficient-direct-image-square`). No holes added and zero
`sorry` left in the delivery. The two new theorems
`AlgebraicGeometry.Scheme.coefficientDirectImageRestrictionCube` and
`CategoryTheory.exactRestrictionDerivedIdentityUnit` are fully proved, as are all
private helpers. This is a proof, not a decomposition into unproved obligations.
Server compilation passed for all three files: ordinary cube 41.7 s, exact-derived
identity unit 2.0 s, and item 24.9 s. Added explanatory comments for the two
scoped heartbeat settings to resolve the only style warnings before delivery.

## No longer needed

No original imports removed and no dependency nodes or modules withdrawn.
Both original proof dependencies remain needed. The generic normalized cube
already supplies the derived pasting argument, so no further coefficient-compatibility
obligation is introduced. No unit-level route changes.

## Where the brief, the DAG or earlier work was wrong

The DAG's proposed derived-unit uniqueness argument is valid. It did not identify
the already proved generic normalized-cube lemma that carries out the required
pasting, including exact-localization factors. The proof now specializes that result.
The supplied HEq normalization suffices after substituting the presentation equalities.
The repository brief's older blanket prohibition on splitting slow files is superseded
by the current worker brief's instruction to improve unfolding first, then move a
self-contained part into a new module when needed.

## New nodes

`lem-pbc-coefficient-direct-image-restriction-cube`, in
`Sheaf.Paper.CoefficientDirectImageRestrictionCube`: the ordinary comparison cube,
proved by the known identity-on-sections formulas and sheaf-morphism extensionality.
This statement contains no derived square or normalization hypothesis.

`lem-pbc-exact-restriction-derived-identity-unit`, in
`Sheaf.Paper.ExactRestrictionDerivedIdentityUnit`: exact derivation carries an ordinary
identity comparison to the expected whiskered derived unit. The proof uses the
existing composition, whiskering and unit laws of exact-derived functors. It also
contains a proved private cancellation lemma for inverting normalized squares.
No change records are needed: no other existing module or its node is changed.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
