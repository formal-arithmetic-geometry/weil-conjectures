## What changed

Proved `ellAdic_localizing_canonical_rightAdjoint_obj_isBounded` in
`Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded`. The proof adds proof-only
imports and private helpers for coefficient normalization, constructibility transport,
transport from normalized finite subfields, the integral coefficient comparison, and
equality of localizing hulls.
It applies `exceptionalInverseImage_exists`, identifies the proper compactification
functor with derived pushforward, transports the adjunction through fully faithful
inclusions, and transfers finite-Tor boundedness to the canonical Brown right adjoint.
The supplied-adjoint theorem and all public signatures are unchanged. This restores and
checks the earlier D3 proof after its batch rollback, with its slow field universe-lifting
helper replaced by transport from the existing finite-subfield lemma. The resulting
module and its unchanged direct consumer
`Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible` both compile using
`lcompile.py --all` (28.9 seconds and 6.1 seconds respectively). The final item also
passed the delivery compiler and server preflight in dry-run commit `15e8a0ef3a`;
later diagnostic runs showed timeouts in adjunction restriction. Supplying its inclusion
and restricted-functor arguments explicitly reduced the full-module compile to 32.5 seconds.

## Proved and sorry left

Closed the original hole
`AlgebraicGeometry.ProEtale.CondensedRing.ellAdic_localizing_canonical_rightAdjoint_obj_isBounded`
(node `lem-sfb-adic-localizing-exceptional-bounded-canonical`). The existing theorem
`ellAdic_localizing_rightAdjoint_obj_isBounded` remains proved. There are zero `sorry`s
left in the delivered module and zero split-off statements.

## No longer needed

Removed the circular canonical-node dependency on
`lem-sfb-adic-localizing-exceptional-bounded`; the canonical proof uses the geometric
`sk-thm-existence` route and the listed coefficient-comparison nodes. No module is
withdrawn. Direct separate rational/integral restriction imports and a duplicated
finite-affine-cover argument are unnecessary because `exceptionalInverseImage_exists`
provides the preservation theorem used here.

Removed proof imports `Sheaf.Paper.BrownHypothesesGeneration` and
`Sheaf.Paper.FiniteCoefficientDescentTwoColimit` from the earlier proof packet; the small
sectionwise coefficient isomorphism and free constant-model constructions are now proved
locally, and neither global theorem is needed. Removed their DAG proof dependencies
`det-brown-hypotheses-generation` and `sk-thm-sfb-qlbar-two-colimit`. No new nodes.

The earlier proof imported `Sheaf.CategoryTheory.Triangulated.LocalizingFunctor`, which
was subsequently deleted as dead code. Its five proved closure and coproduct-universe
helpers are now private lemmas in the item; no deleted module is reintroduced and neither
of its public functor theorems is added. The node dependency
`det-proper-image-localizing-principle` is no longer needed.

## Where the brief, the DAG or earlier work was wrong

The canonical node previously depended on the supplied-adjoint boundedness node,
while that theorem depended on the canonical node, creating a circular proof plan.
The proof and node records now use the geometric existence theorem and explicitly record
the coefficient and localizing-hull comparisons needed by the implementation.

The required change record is `coord/changes/ell-adic-exceptional-bounded-local-helpers.md`.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
