## What changed

Replaced the hole in `AlgebraicGeometry.Etale.LocallyClosedHomGenerator.normalizedComparison`
by an ordinary-etale reduction. The existing shriek comparison supplies exceptional
constructibility, its actual coefficient map and its counit equation. The new direct-image step records conversion of the composite comparison to the
factorized ordinaryComparison by canonical compositors. The new cancellation step
records precomposition of the pairing-change equation with the mapped inverse,
preserving the exact evaluation-normalized word.

Four genuine steps are split off. The first two are: the local finite-projective Hom calculation and
invertibility of the specified internal adjunction. The first contains no immersion,
exceptional adjoint, direct image or normalized comparison. The second contains no
coefficient change or constructibility assertion. The remaining two are the ordinary locally closed direct-image comparison and cancellation of the pairing equation. The item combines their conclusions
with the existing shriek, direct-image and pairing-change theorems. All existing signatures remain unchanged. The inverse is constructed directly from
invertibility of the specified internal adjunction; it equals the old totalized construction. The normalization predicate now applies a
generic categorical mapped-word predicate to the identical factors and equality, making its
constructor independent of geometric instance normalization. This proved support module
is `Sheaf.Paper.NormalizedComparisonWord`; it adds no hole. No adopted source-library module is edited.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.LocallyClosedHomGenerator.normalizedComparison`
(node `lem-coef-locally-closed-hom-generator`). Its proof has no internal hole.

Added four named remaining holes, each with proof exactly `by sorry`:

- `AlgebraicGeometry.Etale.locallyProjectiveCoefficientHom`, in
  `Sheaf.Paper.LocallyProjectiveCoefficientHom`, node
  `lem-coef-locally-projective-coefficient-hom`.
- `AlgebraicGeometry.Etale.locallyClosedInternalAdjunction_isIso`, in
  `Sheaf.Paper.LocallyClosedInternalAdjunctionIso`, node
  `lem-coef-locally-closed-internal-adjunction-iso`.

- `AlgebraicGeometry.Etale.CoefficientPairingChange.pairingCancellation`, in
  `Sheaf.Paper.LocallyClosedPairingCancellation`, node
  `lem-coef-locally-closed-pairing-cancellation`.
- `AlgebraicGeometry.Etale.locallyClosedOrdinaryComparison_isIso`, in
  `Sheaf.Paper.LocallyClosedOrdinaryComparisonIso`, node
  `lem-coef-locally-closed-ordinary-comparison-iso`.

The packet has zero holes in the item and four in new modules: one closed, four added,
net minus three. This is a decomposition, not a net proof closure.

## No longer needed

Removed the redundant private import `Sheaf.Paper.FiniteCoefficientDirectImage`
(already public through the existing shriek and pairing imports). Removed private imports `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
and `Mathlib.Topology.KrullDimension`; the proof needs no Krull-dimension calculation.
Also removed private imports `Mathlib.AlgebraicGeometry.Noetherian`,
`Mathlib.Topology.NoetherianSpace` and `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`;
the geometric checks are encapsulated by the ordinary-comparison step.
The original public imports are retained; the internal-adjunction invertibility module
is additionally public because the inverse construction uses it.

The new proof does not use `lem-coef-finite-hom-domain-calculus`,
`lem-coef-etale-lisse-hom-reduction`, `lem-kun-dimension-finite-type`, or
`def-kun-topological-krull-dimension` as proof dependencies. The shriek comparison already
gives the exceptional object's finite-Tor constructibility; the local-projective argument
works directly for its given second argument and needs no dimension bound. The latter
calculation has different local-system and Hom presentations from the old specialized
lisse-reduction theorem. The finite-dimensional-bound tool approval is removed from this
node. Existing declaration-level coefficient and constructibility dependencies remain.
No module is withdrawn; these dependency removals are local to this proof and do not
assert that other parents no longer need them.

## Where the brief, the DAG or earlier work was wrong

The old plan's Step 5 attributed invertibility of I_A and I_B to
`internalAdjunction_pairing_change`, whose Lean conclusion only gives PairingChangeEquation.
The new internal-adjunction lemma states the missing proper/open projection mate step.
A direct proof and a generic mate proof were attempted; the concrete functor-presentation
conversion still needed work at the delivery checkpoint. The old plan also hid the
passage from the direct-image comparison for j≫g to its factorization; the new ordinary-comparison obligation records the published composition theorem
and cancellation of its two compositors.

The current blueprint finite-Hom proof is in
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-tower/`, rather than the
older source path in the original node. It uses site-perfect generators; the assigned
statement is its degree-zero local-projective case. No unit statement or target changes.
Edge cases checked for the local statement: empty scheme or cover, rank zero,
projective summands, zero ring, identity coefficient map and nonflat quotient maps.
The Tor window is that of the second argument, so varying local ranks create no
unbounded-degree issue. The internal-adjunction statement also permits arbitrary
unbounded objects and empty schemes, as do its proper/open projection ingredients.

## New nodes

`lem-coef-locally-projective-coefficient-hom` records the local finite-projective Hom
calculation with arbitrary finite rings and the published evaluationComparison arrow.
It is strictly the local step. Its proof uses K-flat resolutions with flat terms,
rather than the specialized finite-coefficient bounded-flat-model theorem. The old
lisse reduction also includes exceptional geometry and dimension-dependent bounds;
the underived finite-projective pullback-Hom lemma changes schemes, not coefficients.
Three Mathlib searches and the current blueprint search found no matching statement.

`lem-coef-locally-closed-internal-adjunction-iso` records invertibility of the exact
internalAdjunction using the proper/open projection and its conjugate. Mathlib's
`conjugateEquiv_iso` handles the generic categorical step; the new obligation is the
geometric specialization and identification with the stated arrow. It is independent
of the other local step and strictly smaller than the item. Three searches are recorded.
The proof-context and import-pruning record is
`coord/changes/W3-locally-closed-hom-proof-context.md`.

`lem-coef-locally-closed-pairing-cancellation` is only the cancellation equality, without
constructibility or any new isomorphism claim. `lem-coef-locally-closed-ordinary-comparison-iso`
is the finite-stage composite-immersion direct-image step, with no local system, internal Hom
or normalization claim. Both are proper subarguments of the original theorem.

`def-coef-normalized-comparison-word` attaches the proved generic categorical predicate
and its constructors, mapped-word/equation wrappers and proved abstract cancellation lemma. It introduces no sorry and unfolds to the previous conjunction.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
