## What changed

Proved `CategoryTheory.ringedFiniteFreeHomBaseChange_complex` in
`Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeData`, without changing its statement,
the scalar-section definition, or any public imports. Added private proof imports of
`ScalarHomOrdinaryTensorComparison`, `ScalarHomExtensionKFlat`,
`RingedTopoiCanonicalTensorPullback`, and `TensorColimitsIndependentCoefficients`.
The existing private import of `ScalarInternalHomAdjunction` is retained.

The proof identifies the supplied extension functor with the normalized scalar pair
by its object and map equations. It totals the existing ordinary tensor comparison,
proves simultaneous naturality on all summands, and proves the requested pure-section
formula using unit naturality and the ordinary tensor formula. K-flat preservation is
the existing theorem for this scalar pair. Standard derived-category choices used to
obtain the pair do not occur in the conclusion. Two fully proved private helpers
establish factorization of tensor maps and naturality of the total comparison.
The tensor-complex node now records this route and its actual dependencies.

Validation: the resumed module compiled through `lcompile.py` in 36.0 seconds
with exit code 0 and no errors or warnings. Explicit congruence in the final
unit-normalization equality avoids rewriting through the expanded total tensor.
The resumed preflight flagged file-level namespace/universe commands; namespace
openings are now scoped to private helpers and the theorem proof, and the helpers
reuse the original universes. The interface comparison reports no changes.

## Proved and sorry left

Closed one original hole:
`CategoryTheory.ringedFiniteFreeHomBaseChange_complex`
(node `lem-sf-ringed-finite-free-tensor-complex`).

Original holes: 1. Closed: 1. Added: 0. Split off: 0. Remaining in the delivered
module: 0. All private helpers are proved. Existing imported results are reused;
this report does not claim to close their transitive proof obligations.

## No longer needed

None. No imports, nodes or modules are removed. The original scalar-adjunction
dependency is still needed to obtain the normalized ordinary pair. Its derived
Hom comparison, derived tensor normalization and tower coherence are not used by
this proof. The total comparison uses the already proved generic chain-map and
coproduct-isomorphism helpers, without re-proving any derived descent theorem.
All four added private imports are used. Public imports and the unit route stay
unchanged.

## Where the brief, the DAG or earlier work was wrong

The former plan offered component chain isomorphisms but did not supply their
simultaneous naturality as a field. The implementation instead uses the existing
normalized ordinary tensor comparison and explicitly proves naturality after
totalization. This is the same mathematical scalar tensor construction, with
all differential signs handled by the existing `tensorPullbackTotal` theorem.
The proof adds no finite-free or flatness hypothesis and covers zero rings and
unbounded complexes. No definition repair, forced consumer adaptation, or new
statement is needed.

## Second reading by X2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
