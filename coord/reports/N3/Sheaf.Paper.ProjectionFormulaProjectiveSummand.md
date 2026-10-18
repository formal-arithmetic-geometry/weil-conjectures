## What changed

The item constructs the finite-free single complex and its explicit strict-perfect
package, transports the displayed splitting through `singleObjXSelf`, and proves
both inverse equations by naturality and the existing finite-free theorem.
Naturality at the identity map, with the two packages, proves equality of pairs.
The existing public theorem signature and degree-zero arrow definition are unchanged.
A new public import supplies the proved `CategoryTheory.cochainTensorHasMapBifunctor`
API lemma. Its local instance attribute avoids repeatedly unfolding total tensor
existence while elaborating the original interface; no data construction changes.
The large functions are bound once and their category parameters are explicit.

The new module `Sheaf.Paper.ProjectionFormulaCoefficientNaturality` states the
naturality of both arrows in a bounded strict-perfect coefficient complex. This
is a proper part of the argument: it asserts no inverse identities. Its docstring
gives the complete natural-language proof, including the inverse-total and mixed
representative squares. Change record:
`coord/changes/projection-formula-summand-proof-context.md`.

## Proved and sorry left

Original hole removed: `SheafOfModules.ringedProjectionFormula_projective_summand`
(one of one in the item), proved from coefficient naturality and the existing
finite-free theorem. The private `map_retract`, `conjugate_retract`, `map_id_pair_retract` and
`inverse_pair_of_retract` are proved. The private `singleFreePackage` is an explicit
construction, with a proof of its splitting in every degree, including rank zero.

One new hole remains: `SheafOfModules.ringedProjectionFormula_coefficient_naturality`,
node `lem-weil-pbc-projection-formula-coefficient-naturality`. It needs the inverse
total-mate naturality square and naturality of the mixed tensor representatives,
transported through epsilon and eta. Forward naturality is the naturality axiom
of the derived projection-map natural transformation.

Validation: the three-module reduction compiles in import order. The proved
existence API takes 1.7 seconds, the naturality statement 39.4 seconds, and the
completed summand proof 54.7 seconds, each below the fixed 60-second limit.
The unchanged `Sheaf.Paper.ProjectionFormulaTotalization` consumer compiles
against the delivered overlay in 6.4 seconds. Normalized source comparison
confirms the original theorem signature and degree-zero definition are identical.

This is a decomposition: one upper hole closed, one lower hole added, net zero.
No other hole is added and no definition contains a hole.

## No longer needed

Removed the redundant direct proof import
`Sheaf.Paper.RingedTopoiCanonicalTensorPullback`, already publicly imported by the
arrow module. No module is pruned from the target import closure. The parent
node's naturality dependency now passes through the new node; the finite-free
node and arrow definition remain needed. Inverse uniqueness in the old final
step is replaced by naturality at the identity and product extensionality.
The unit's route is preserved.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The DAG's retract computation needs naturality of
the reverse arrow as well as the forward arrow. The new node makes this input
explicit and supplies its chain-level and representative proof in words.

## New nodes

`lem-weil-pbc-projection-formula-coefficient-naturality` isolates the naturality
step of lemma 1266, read with definition 1264 in the current blueprint. It permits
arbitrary cochain maps and two unrelated packages; packages supply only proofs of
flatness, K-injectivity and invertibility. Identity maps, zero maps, and rank-zero
packages satisfy the statement. Its proof uses the existing canonical tensor
comparison, inverse-total isomorphism, uniquely specified mixed representatives,
and K-flat resolutions. It does not assert the inverse conclusion of the item.

`lem-weil-pbc-cochain-tensor-has-map-bifunctor` is proved by Mathlib's existing
coproduct instance, in its own module. It caches the total-existence proof in the
public interface, so no private declaration occurs in a public signature.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
