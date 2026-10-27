## What changed

Replaced the hole in `WeilConjectures.IntegralVerdier.finiteIntrinsicVerdier_biduality`
by a geometric proof from finite-stage Verdier biduality and the normalized constant-ring
bidual comparison. The statement is unchanged. Proof imports are private.

The proof takes the inverse realization of M, transfers its intrinsic constructibility
and its supplied Tor interval using the realization counit, applies the existing
fixed-scalar finite-stage biduality theorem, constructs the comparison with the actual
`integralDualizingFiniteTerm` from the regular-unit comparison and the equivalence unit,
and cancels the input and double-dual comparison isomorphisms.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.IntegralVerdier.finiteIntrinsicVerdier_biduality`
(node `lem-sf-finite-intrinsic-verdier-biduality`).

Added one structural hole:
`WeilConjectures.IntegralVerdier.finiteIntrinsicBidualComparison`
(node `lem-sf-finite-intrinsic-bidual-comparison`), in the new module
`Sheaf.SixFunctors.FiniteIntrinsicBidualComparison`.
This is a decomposition, not a net reduction in hole count: one original hole closed,
one strictly smaller structural hole added. The remaining statement compares two actual
normalized arrows for arbitrary W and K over any finite commutative ring. It assumes
neither geometric hypotheses nor constructibility nor Tor bounds nor invertibility of
either arrow; the geometric biduality theorem is applied in the original module.
No sorry occurs in a definition, private helper, or partial proof.

## No longer needed

The direct proof dependencies `lem-sf-proetale-constructible-origin` and
`lem-sf-comparison-tor-amplitude` are unnecessary here. The fixed-scalar finite-Tor
predicate is defined by intrinsic realization, and its input can therefore be obtained
from M through the equivalence counit; no etale origin or Tor reflection argument is
needed. No imports were removed from the original module.

`lem-weil-finite-duality-site-comparison` and `lem-weil-duality-pairing` are still needed
by the finite-stage theorem and the structural comparison respectively; they are not
claimed globally pruned. No module is withdrawn. The unit route is retained by applying
`thm-fix-general-biduality`; the unit record has empty realized statement and steps.

## Where the brief, the DAG or earlier work was wrong

The original plan's first step takes an unnecessary detour through etale origins.
The canonical fixed-scalar predicate already uses the intrinsic realization.
The geometric theorem's declarations do not themselves provide the comparison with an
arbitrary normalized intrinsic tensor presentation. The new structural node states that
missing coefficient-realization step with arbitrary dualizing object, independently of
finite-stage geometric biduality.

The new node uses the ordinary total-tensor realization lemma
`lem-exc-intrinsic-realization-tensor-complex` as a structural tool from another unit:
its exact constant-scalar realization is the one used here. The biduality unit contains
no substitute for this coefficient-presentation comparison. No unit step is bypassed.

## New nodes

`lem-sf-finite-intrinsic-bidual-comparison` records the remaining comparison of signed
evaluation transposes under the exact constant-ring realization, including arbitrary
isomorphisms of the input and dualizing object. Source: the realization step in the
original node's proof; Stacks 00YV, 06YL, 08J9 and 08JA. Its docstring gives the generator,
K-flat localization, tensor-Hom, and transposition argument. Edge cases checked in words:
zero ring, zero objects, and empty sites; no perfectness assertion is made.
No existing statement or definition changes, so no change record is needed.

## Second reading by J9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
