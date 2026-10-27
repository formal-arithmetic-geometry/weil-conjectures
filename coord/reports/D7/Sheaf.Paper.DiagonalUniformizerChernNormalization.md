## What changed

Replaced the proof of `diagonalUniformizer_chernNormalization` by a complete assembly
of a local coefficient calculation and canonical model-adjunct coherence. Its signature
and original public import are unchanged.

The private `completed_local_lift` constructs the local completed arrow on P. Completeness
of its unit and shifted line, fullness of completed scalar restriction, and cancellation
prove its actual root-limit normalization. The private `ordinary_positive_adjunct` proves
the final finite adjunct identity from the defining second component of the positive
decomposition and naturality of its comparison mate.

The main proof uses `s.hc` directly, constructs the two normalized arrows as an explicit
`NormalizedAdjunctPair`, applies coherence and the local Kummer comparison, unfolds their
equation predicates, and finishes with the finite adjunct identity. Equality is carried
through adjunction by `ordinary_positive_adjunct_of_eq`; `commutes_of_transport_eq`
substitutes it at abstract coefficients. The final inline tactic copies the coefficient
parameters and class instances already carried by the diagram type, and builds the
application of that proved helper. This avoids costly instance elaboration and record
unfolding. The resulting proof term is checked by Lean. No trace or degree assumption
is introduced.

The new endpoint and condition modules contain actual constructions and explicit
predicates, with zero holes. Unit inversion is constructed by composing the supplied
isomorphisms at abstract coefficients. Named predicates and the pair structure keep
concrete coefficient and shift instances out of the exported theorem types. The main
proof unfolds those predicates when it uses their equalities.

## Proved and sorry left

This is a decomposition, not a net closure of the obligation.

Closed the original textual hole:
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalUniformizer_chernNormalization`.
There are zero textual holes in the assigned module.

Added two whole public theorem holes:

- `AlgebraicGeometry.ProEtale.DiagonalCoefficients.UniformizerChernNormalizationData.localChern`
  (`lem-diagonal-uniformizer-local-chern`). Its output is the positive finite Kummer
  equation on P, before direct image.
- `AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalUniformizer_adjunctTransport`
  (`lem-diagonal-uniformizer-adjunct-transport`). Its output identifies the image of the
  canonical completed adjunct with the adjunct of the local coefficient image. It does
  not identify that local image with the finite Kummer class.

One upper hole is closed and two distinct lower holes are added, net minus one. Neither
lower statement alone is the assigned theorem. The completed local lift and final finite
adjunct calculation are proved directly, rather than split off.

Validation: all four supporting modules compiled with artifacts through `lcompile.py
--all`. The complete main proof compiled in 26.1 seconds; its only warnings were the
temporary profiling options, now removed. `deliver3.py` performs the final compile,
axiom, hole and packet checks.

## No longer needed

No module or original public import is withdrawn. No globally pruned module is claimed.

The old plan's use of `diagonalTrace_completedChern_lift` is replaced by the proved local
lift. Its module remains necessary for `systemChern` in the unchanged input record.
`sk-lem-geo-cartier` is no longer a direct proof dependency: the local step uses the
ordinary line-bundle Kummer class, without its supported Cartier refinement. The other
original coefficient definitions remain necessary.

## Where the brief, the DAG or earlier work was wrong

No statement dispute or unit-route change. The rework archive and Lean attachment are
preserved; no quarantined module is withdrawn. Searches found finite tower Kummer
realization and finite adjunct calculations, but no result comparing the completed local
class through these prescribed uniformizer endpoints.

The input already supplies the normalization against the canonical `systemChern`.
Retaining that expression also retains the actual shift instance of `model.chernAdjoint`;
its expansion through a newly elaborated strict-system shift was not definitionally
compatible. Coherence now uses the exact input equation and its identity-model field.
This keeps the two mathematical steps separate and requires no change to shared types.

Edge cases checked in the new statements: n=0, empty Y, zero coefficient objects, and
ramified quotients subject to the supplied annihilator condition. The new data structures
store only explicitly supplied arrows and their two original normalization proofs; no
coefficient-transport equation or arbitrary existence witness is a field.

## New nodes

`def-diagonal-uniformizer-local-endpoints`: the fourfold local coefficient functor,
composite unit isomorphism and its inverse, shifted positive-line endpoint, and explicit
`LocalChernNormalized` equation predicate. All have actual definitions, without holes.

`def-diagonal-uniformizer-adjunct-conditions`: the root-limit and canonical system-Chern
normalizations, the generic four-step equation `TransportTo`, the structure storing the
two normalized arrows, and its explicit `Transported` predicate. These isolate the type
expressions from the theorem; they assert no compatibility theorem.

`lem-diagonal-uniformizer-local-chern`: local completed-to-finite positive Kummer
normalization through the constructed endpoints. Its conclusion contains no pushforward.
The record s retains the original types, but its completed adjunct c and hc are not used
in the local equation.

`lem-diagonal-uniformizer-adjunct-transport`: coherence of the four normalized comparisons
for the actual model adjunct. It uses the endpoint definitions and the canonical
normalization, independently of the local finite Kummer theorem.

No existing shared definition, signature, instance or visibility is changed. No change
record or consumer adaptation is required.

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
