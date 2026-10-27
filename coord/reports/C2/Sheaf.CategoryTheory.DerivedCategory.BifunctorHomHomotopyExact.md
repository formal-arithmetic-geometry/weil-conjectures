## What changed

Proved `CochainComplex.bifunctorHomHomotopyFunctor_leftOp_exact` without changing
its statement or any existing public import. Added private proof imports for the
stated signed cone comparison and Mathlib's opposite triangulated functor APIs.
The private helpers construct the signed shift maps, prove their chain-map,
inverse, naturality, zero and addition identities, identify the image of a cone
triangle with the opposite mapping-cocone triangle, and descend through the
homotopy quotient and derived localization. The final step takes `leftOp`.

## Proved and sorry left

Closed the one original hole:
`CochainComplex.bifunctorHomHomotopyFunctor_leftOp_exact`
(node `lem-sf-bifunctor-homotopy-exact`). No holes added or split off; no `sorry`
remains in the delivered module. The proof uses the existing declared dependency
`CochainComplex.exists_signedBifunctorConeIso`
(node `lem-sf-signed-bifunctor-cone-iso`), whose proof is outside this delivery.

## No longer needed

None. The proof follows the stated signed shift/cone route and retains all its
mathematical dependencies. No public import, node, module or source declaration
is withdrawn.

## Where the brief, the DAG or earlier work was wrong

None. Mathlib's opposite triangle equivalence lets the cone calculation be done
into the opposite derived category first; taking `leftOp` then yields exactly
the original assertion. This is the same cone and localization argument as the
node, with no stronger hypothesis and no changed definition.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
