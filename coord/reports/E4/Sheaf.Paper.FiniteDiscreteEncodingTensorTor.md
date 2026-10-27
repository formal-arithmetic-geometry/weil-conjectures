## What changed

Completed the argument for `AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.encoding_tensor_tor`
without changing its statement. Private proved helpers assemble the ordinary strong monoidal
structures from the existing section-action comparison, ring-isomorphism scalar transport and
constant-scalar restriction. Exact monoidal derived descent supplies the first conjunct on the
actual termwise equivalence. The native Tor-amplitude transport theorem supplies preservation
and reflection for both equivalences.

A private resolution comparison identifies the intrinsic `HasProEtaleTorAmplitude` predicate
with generic derived Tor amplitude. It covers every representative and every K-flat resolution
in the forward direction; the reverse direction uses an existing flat-term K-flat resolution.
The degree-zero test module is unrestricted, and the given inequality supplies exactly the
ordered-interval condition. No nonzero-ring, boundedness or constructibility assumption is used.

The complete proof compiled in 22.1 seconds. Local instance priorities match the ambient
coefficient braiding, and local irreducibility keeps the closedness construction behind its API.

All added imports are private proof imports. The existing public import is unchanged.
The existing node's proof, proof dependencies and proof origin follow this argument.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.encoding_tensor_tor`
(node `lem-sf-finite-discrete-encoding-tensor-tor`), one original hole.
Added: none. Remaining holes in the delivered module: none. Split off: zero.
Every private helper is proved. Imported declarations retain their existing obligations.

## No longer needed

No original import was removed: the module had only its required statement import.
Three redundant proof imports were removed after checking their public-import paths:
`WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat` and
`WeilConjectures.Algebra.Homology.HomotopyCategory.Braided` are already exposed by the
statement import, and `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel` is exposed
by the Tor-amplitude transport import.
The proof does not need `sk-def-sfb-constructible` or its constructibility conditions.
The former proof dependencies `def-sfb-modobj-relative-tensor`, `sk-def-sfb-sheaf-tensor`,
`def-pur-sheaf-tensor-product`, `def-sfb-preserves-kflat-quasi-iso` and
`def-weil-derived-tensor` need no separate direct proof citation: the existing comparison
and native derived-category APIs already use the prescribed tensors. Their definitions
remain in the statement import closure and are not withdrawn. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned tensor transport is available through the existing library APIs, so there is
no need to repeat the balanced-pairing or signed-total constructions in this module.
The resolution-based intrinsic Tor predicate is not definitionally the generic predicate;
the proof supplies its representative comparison explicitly.

The current source file exists despite the historical quarantine/rework row, and the unchanged
baseline compiled successfully. Its Lean attachment and all public declarations are preserved.
The unit route is unchanged; this is the coefficient-comparison component below that route.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
