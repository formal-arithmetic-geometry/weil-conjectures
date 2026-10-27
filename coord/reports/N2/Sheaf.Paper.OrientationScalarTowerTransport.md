## What changed

Filled all four theorem bodies in `Sheaf.Paper.OrientationScalarTowerTransport` without
changing any existing signature or definition. The finite scalar proof pastes the given
mixed square and normalizations, uses naturality and the Tate scalar/pullback square,
and cancels the pulled-back scalar isomorphism. Its second equation follows by
cancelling the primed orientation.

The evaluation proof lifts through the fully faithful composite of the single functor
and shift, transports exact evaluations through an explicit natural isomorphism, and
uses component extensionality of strict systems. It keeps the independent scheme and
coefficient universes. The tower proof conjugates the orientation endomorphism to a
shifted single, applies this detection result, and cancels the conjugating isomorphism.
The ramification proof identifies the associated uniformizer exponent with
emultiplicity and then takes powers of equal principal ideals.

Added the proof imports `Sheaf.Paper.TateScalarPullbackCoherence` and
`Sheaf.Paper.PulledOrderedLineSingle`, each with one strictly smaller remaining step,
a source, a proof in words, and a node. The first contains no dualizing object or
orientation; the second is an object-presentation result with no exceptional mate or
map-equality hypothesis. Updated the original node's proof and proof dependencies.
No existing public import was changed, and no consumer adaptation is necessary.
The evaluation proof disables the small-site sheafification instance only for its
own theorem command, so that the existing independent-coefficient instance is used.

The resumed delivery check on 2026-10-26 reached all packet modules: the
published dependency object missing in earlier attempts is available again.
Both helper modules compiled. The item check exposed an ambiguous finite-level
category, the incorrect name `Functor.image_preimage`, and unused simplifier
arguments. The evaluation proof now supplies the finite-level category and its
independent universes explicitly and uses `Functor.map_preimage`; the unused
arguments were removed. Naturality is composed as explicit equality terms to
avoid rewriting through unfolded system evaluations. The revised item passed its
single-file compile in 27.3 seconds. Its remaining empty-line style warning was
removed before the final delivery check. Both helper modules passed the preceding
delivery compile. No proof or publication error remains known; the final delivery
runs the complete compile, axiom probe, and preflight checks.

## Proved and sorry left

Four original `sorry` bodies replaced, with two holes added: net two holes
closed. Two original proofs are completed from existing declarations, and two are decomposed through smaller
statements. All four original declarations are in
`AlgebraicGeometry.ProEtale.OrientationTransport`, node
`lem-sp-orientation-scalar-tower-transport`:

- `shifted_tower_evaluation_injective`: completed from Mathlib single/shift full
  faithfulness, exact-derived comparisons, and strict-system extensionality.
- `ramified_coefficient_level`: completed from the recorded DVR theorem and Mathlib
  association, multiplicity, and principal-ideal identities.
- `finite_scalar_transport`: complete combining proof using the new Tate square.
- `tower_orientation_transport`: complete combining proof using the new shifted-single
  presentation and the completed evaluation detection theorem.

No `sorry` remains in the item module. The two added holes are exactly:

- `AlgebraicGeometry.ProEtale.tate_scalar_pullback_coherence`, node
  `lem-sp-tate-scalar-pullback-coherence`, module
  `Sheaf.Paper.TateScalarPullbackCoherence`.
- `AlgebraicGeometry.ProEtale.pulled_ordered_line_single`, node
  `lem-sp-pulled-ordered-line-single`, module `Sheaf.Paper.PulledOrderedLineSingle`.

These are decompositions, not four proofs from already completed dependencies.

## No longer needed

Removed the private imports `Sheaf.SecSmoothPurity.DirectImageScalarOperations` and
`Sheaf.AlgebraicGeometry.ProEtaleConstantExact`. The finite proof uses the actual
`scalarPullbackProEtaleIso` in its hypotheses, not the separately typed
`directImageScalarPullbackIso`. Thus `def-sp-constant-scalar-pullback-comparison` is
not a direct proof dependency of this node. The exact tower pullback is already part
of the supplied geometry; its single-degree effect is isolated in the presentation
lemma rather than reproved through a finite exactness theorem in the item module.
Accordingly `prop-weil-pbc-proetale-constant-exact` is no longer a direct proof
dependency here; its obsolete top-level tool approval is removed from this node.
No global withdrawal is claimed.

The original proof dependencies `def-weil-abstract-derived-category` and
`def-coefficient-twists-detailed` are no longer separately cited in the argument:
Mathlib's single/shift and exact-derived APIs supply the former, and the specified
ordered-line presentation isolates the latter. The original public imports and all
statement dependencies are preserved. No module is withdrawn, and there is no claim
that a dependency used by another consumer is globally unnecessary.

## Where the brief, the DAG or earlier work was wrong

The finite proof plan suppresses the Tate scalar/pullback compatibility square.
Naturality on the orientation alone does not supply that square: the supplied
normalized root and coefficient maps must be shown compatible. The new Tate-line
lemma states precisely this missing part, separately from the orientation argument.
The existing `FiniteTateBalancedScalarPullback` covers the unit and first root line
in etale coordinates, but does not directly state the ordered-power pro-etale square
for the supplied comparison records.

The tower plan also needs an actual shifted-single presentation of the pulled-back
ordered line. Equality cannot be detected by evaluations for arbitrary derived
morphisms. The new presentation lemma states only the needed object assertion;
the item then proves the map equality by conjugation and shifted-single detection.
The coefficient prime is explicitly required invertible in that lemma.

The new statements were checked at d=0, at the first tower level, for zero coefficient
rings in the finite square, and without unramifiedness or tower normalization.
At d=0 the square is the scalar/pullback unit square and the presentation is exact
pullback of a coefficient unit. Positive N makes the common-exponent root map the
identity, including N=1. No arbitrary witness is selected from an unproved existence
statement in a definition; the presentation's existential is used only in a proof.

The ramification proof uses `lem-weil-l-adic-extension-integers-dvr` as the
general coefficient DVR tool already underlying the recorded ring and uniformizer.
The new nodes use the following existing results from other units as tools, rather
than replacing any unit route: `lem-sp-finite-tate-balanced-scalar-pullback` for the
unit/first-root square, `lem-asd-etale-finite-twist-pullback` for normalized root
pullback, `lem-sfb-etale-proetale-scalar-pullback-cube` for site transport,
`lem-pc-kflat-closure` and `lem-weil-pbc-cochain-pullback-tensor-shift` for the tensor
representatives and shifts, and `lem-sf-exact-functor-derived-triangulated` for exact
singles and shifts. Their statements were read; none states the entire new result.
The unit's orientation and tensor-factor route is preserved.

## New nodes

`lem-sp-tate-scalar-pullback-coherence` is the normalized coefficient/geometric
pullback square for the ordered finite Tate line alone. Its module is
`lean/Sheaf/Paper/TateScalarPullbackCoherence.lean`. Its proof in words reduces to
root-map uniqueness, balanced generator equations, tensor/shift induction, and the
published etale/pro-etale cube. Searches found algebraic base change and ordinary
module results, but no matching derived sheaf statement.

`lem-sp-pulled-ordered-line-single` states that exact pullback of the specified
ordered tower line has a presentation F[0][2d]. Its module is
`lean/Sheaf/Paper/PulledOrderedLineSingle.lean`. Its proof uses levelwise flatness,
the K-flat tensor computation and exact realization/pullback comparisons.
Searches found exact-derived shift and single APIs, but no matching object statement.
Neither new dependency has a path back to the item in the recorded dependency graph.
There are no definition or statement changes and no change records.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
