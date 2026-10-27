## What changed

Reduced `AlgebraicGeometry.ProEtale.integralModelsEmbeddedStacksCriterion` to the
existing Stacks theorem and two separate coefficient-transport steps. The main
proof constructs the universe-lifted finite-dimensional instance, uses the existing
proved continuous integer-ring isomorphism and the existing absolute-value-to-spectral
`IntegralConstantModel.pointComparison`, and proves preservation and reflection
of bounded constant-model constructibility using exact scalar restriction and its
homology comparison. It then assembles the independent completeness and residue
comparisons with the existing Stacks iff. The statement is unchanged.

The new modules `Sheaf.Paper.EmbeddedIntegralCompletenessTransport` and
`Sheaf.Paper.EmbeddedIntegralResidueTransport` each state one transport theorem.
They quantify over an actual monoid-object isomorphism of condensed rings and use its actual scalar
restriction; no object or equivalence is chosen from an unproved existence result.
The imports of private existing helpers are proof imports only.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.ProEtale.integralModelsEmbeddedStacksCriterion`
(node `lem-sfb-embedded-integral-stacks-criterion`). Its assembly proof is complete.

Two holes added, so this is a decomposition, not a net proof of the original obligation:

- `AlgebraicGeometry.ProEtale.embeddedIntegralCompletenessTransport`
  (`lem-sfb-embedded-integral-completeness-transport`).
- `AlgebraicGeometry.ProEtale.embeddedIntegralResidueTransport`
  (`lem-sfb-embedded-integral-residue-transport`).

No sorry remains in the item module. Each new module has exactly one public theorem
with its whole proof `by sorry`, source, complete proof in words and matching node.
Existing dependencies of the Stacks theorem retain their existing holes.

## No longer needed

No existing module is withdrawn. The sandbox contained an unfinished earlier spectral
transport construction, with four new modules and four unlanded nodes. These are
preserved under `scratchpad/prior-spectral-attempt` and excluded from this delivery: the
existing proved `pointComparison` replaces that attempted reconstruction. No original import is removed: the Stacks theorem
and coefficient comparison both occur in the proof. The direct proof dependency on
`def-sfb-quotient-kernel-completeness` now belongs to the completeness transport node.
The original two general transport paragraphs are replaced by the actual assembly
and the two named transport steps. The embedded completion-equivalence and
etale-residue-origin comparison modules are not imported: the existing spectral
Stacks criterion supplies the criterion itself. The unit route is retained.

## Where the brief, the DAG or earlier work was wrong

The absolute-value and spectral-norm coefficient presentations require the existing
explicit `IntegralConstantModel.pointComparison`; they are not definitionally equal.
The earlier sandbox attempt timed out in its reconstructed spectral data. It is
unnecessary once the existing `pointComparison` is used.
The original proof plan correctly described the mathematics but did not name Lean
transport statements for local completeness and the first residue condition. The
public coefficient comparison provides only existence of an additive equivalence
and forward constructibility, which alone does not identify either scalar square.
Its existing proved private coefficient isomorphism and the existing generic
scalar-isomorphism constructibility iff suffice for the constructibility part.

Edge cases: both transport statements concern arbitrary K, including zero and
unbounded complexes. The completeness statement assumes no residue finiteness or
boundedness; the residue statement assumes no completeness. Any monoid-object
isomorphism of these condensed rings acts pointwise by its map on the one-point profinite set, so preserves
constant functions and the unique maximal ideal. Changing a uniformizer by a unit
changes neither first-quotient kernel. Empty X causes no extra nonempty hypothesis.

## New nodes

`lem-sfb-embedded-integral-completeness-transport` isolates only preservation and
reflection of the local kernel-ideal completeness condition. Its proof uses scalar
squares, slice localizations and the invariance of zero derived internal Homs.

`lem-sfb-embedded-integral-residue-transport` isolates only constructible residue
cohomology and finite Tor amplitude under the first-quotient scalar square. It does
not assert constructibility of the original integral complex. The main theorem
still needs the independently existing Stacks theorem to recover that conclusion.

No definition or existing signature changes; no change record is needed.

## Second reading by Q9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
